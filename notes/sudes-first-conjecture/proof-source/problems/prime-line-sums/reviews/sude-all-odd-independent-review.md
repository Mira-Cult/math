# Independent review of the all-positive-odd-order composition

Reviewer: `/root/controller_redesign/central_completion_review`. I am a
nonauthor of the all-odd manuscript, verifier and scientific manifest. I
changed no producer scientific file or certificate. My earlier CC review
was a separate component obligation; it does not substitute for this
final composition review.

## 1. Verdict and exact assertion

**ACCEPT at scientific revision
`67647907ad0693631f42c169df61cbe46a13a3ff`, tree
`1bc2010ee1b2ffb8e2ec4fbd971040ef76e0204e`.**

For every **positive odd integer n**, exactly the first n² odd primes
can be arranged, each once, in an n-by-n square so that every row sum,
every column sum and both main diagonal sums are prime. Line sums may
repeat. The statement retains the exact input pool and both diagonals;
it imposes no equal-sum condition.

In the requested positive-order tail formulation this gives **N0=1**.
The analytic and construction tail begins at 2001. The separate finite
witnesses cover all 1,000 positive odd orders below that endpoint.

There is no unresolved mathematical, source-identity, case-coverage or
replay finding in this composition. This is ordinary independent agent
mathematical and computational review. It is not external human referee
acceptance, a formal GitHub approval, a proof of the imported analytic
theorems, or end-to-end proof-kernel verification.

## 2. Exact science and accepted prerequisites

All paths below are relative to `problems/prime-line-sums`.

| New scientific file | SHA-256 |
| --- | --- |
| `manuscripts/sude_all_odd_theorem.md` | `c53aa38aa3a474387b357089c765191e60aacedef250f361317a4d61708e4623` |
| `code/verify_sude_all_odd.py` | `a05971f657d5735ac58bb55828c82105b7f0d69f4ab69328eb708e96efc634b2` |
| `inputs/sude_all_odd_constants.json` | `0d4ca1b97404ad620389a4f4f5adec1d327c0106c55fca2e353c85421735d3fb` |

I read both final prerequisite reports, verified their exact file hashes,
and checked their accepted scientific identities. They accept distinct
parts of the theorem; neither report alone accepts this wrapper.

| Prerequisite | Accepted scientific revision | Final independent report |
| --- | --- | --- |
| Every odd n from 1 through 1999 | `5f9c86d1dd8b075547ad5041fb2ee64ebfc59ddf` | [Finite review](cutoff2-finite-remainder-independent-review.md) |
| Every odd n at least 2001 | `48c93bc07d78223d7cec64d0bb1257f11c07c282` | [Tail review](cutoff2-tail2001-independent-review.md) |

The finite review is by `/root/moderate_finite_review` and has SHA-256
`91857c87fb7a27a8f065369f94b2ba3bd7096e6306b5c5b0dedfd6211c541be9`.
Its scientific tree is
`77423d684717a650ccfb03e8688ebbb6f211f9de`, and its manifest SHA-256 is
`18fa6f8d39c5dd70acbfd3d3bb62ce00b36368bbe4f53603cabcefd83910c783`.

The tail review is by `/root/small_analytic_review` and has SHA-256
`a2c2999dfd4578bad35c9d1860d1d753b7599b03a98067e79f67aaf9ddd7dd68`.
Its scientific tree is
`13fc8cd8eb7175b31fa0183d5de1705aa074b6a2`, and its manifest SHA-256 is
`0ae27564e9bd10150bfa24951d2d8f8db39e3e14ae1ba23d40f48d6f0aeac935`.

I also checked the actual Git blobs of these final reports at their later
additive delivery `4cb19e985f13f97fa8812151553574ee787338d2`, tree
`bda443de9148a62a162ab33f20495a022e530357`. Their hashes are unchanged.
That delivery identity is distinct from every scientific revision above.

### Complete source closure

I exported the scientific files directly from Git blobs at the named
67647907 revision, checked the commit type and tree, and compared every
file with its manifest digest and working-tree bytes. The export has
**343 scientific files: the master manifest plus its 342 required files**.
It contained no Git checkout and no uncompressed working certificate.

The exact required set is the union of:

- the tail's 333 required sources and its own manifest;
- the finite verifier's six required sources and its own manifest;
- the new all-odd manuscript and verifier.

The two component source sets share only `PROBLEM.md`. The new master
manifest is additional to that 342-file union. I independently parsed the
literal required sets rather than relying on a successful hash loop over
whatever entries a supplied manifest happened to contain.

All 333 inherited tail source files and the tail manifest match their
actual Git blobs at 48c93bc0. All six inherited finite sources and the
finite manifest match their blobs at 5f9c86d1. The new wrapper therefore
uses exactly the prerequisites that received the final reviews, including
the tail's corrected 5,937-predicate ledger. It does not silently retain
the superseded ledger revision.

## 3. Mathematical case composition

Let n be a positive odd integer, and write n=2j+1 with integer j>=0.
If j<1000, then n is one of 1,3,...,1999, and the accepted finite
certificate supplies the required square. If j>=1000, then n>=2001,
and the accepted complete tail supplies it. These two inequalities on j
are exhaustive and disjoint. The only integer between 1999 and 2001 is
the even integer 2000.

The singleton case is included explicitly. Its input pool consists of
the odd prime 3. The square `[3]` gives prime sum 3 for the row, column
and both diagonal labels. Repetition of the line value is permitted.

Both prerequisites use the same input specification: the first n² odd
primes, with prime 2 excluded and prime 3 first. Each uses every input
entry exactly once and checks both diagonals. The finite verifier's rank
permutation and the tail's entry controller operate on those same
prescribed pools. No target repetition is mistaken for permission to
repeat an input entry.

The infinite case is the **complete** accepted tail, including all its
bounded routes and the preserved unbounded theorem. It is not an
extrapolation of the last bounded controller or a finite collection of
successful endpoint inequalities. The tail reviewer separately checked
the whole-tail parameter envelopes and all joins, including 311743 to
the preserved first relevant odd order 311745. This wrapper adds only
the finite/2001 case split; it introduces no new analytic estimate,
source-domain extension or rounding argument.

The dependency graph is acyclic: the finite witnesses establish their
bounded assertion without using the tail, and the tail establishes its
assertion without using the finite witnesses or this wrapper. Their
union is consequently a valid case proof, not a mutual assumption.

## 4. Full default replay at the exact revision

From the fresh exported problem directory I ran the unmodified default
command:

```sh
python3 -B code/verify_sude_all_odd.py
```

It completed successfully, with no stderr, in approximately 439 seconds
in this environment. Its exact status is
`PASS_ALL_POSITIVE_ODD_ORDERS_FINITE_CERTIFICATE` and its complete output
SHA-256 is

`985f7066edeabdf704b4be3510244cdf1669711ce2bb1dfe2092d222c4d5a1ce`.

This was the full default run. It did not use `--composition-only` or
skip the inherited component executions.

| Actual replay evidence | Result |
| --- | ---: |
| Required root source files, excluding the master manifest | 342 |
| Bound component-source edges | 339 |
| Root malformed-manifest rejection controls | 369 |
| Root physical source attacks | 1,711 |
| Complete prerequisite commands executed | 2 |
| Tail controller/fallback commands executed | 11 |
| Finite square orders replayed | 1,000 |
| Finite cells examined | 1,333,333,000 |
| Finite required line labels checked | 2,002,000 |

The two complete prerequisite statuses are
`PASS_COMPLETE_2001_FINITE_CERTIFICATE` and
`PASS_EXACT_FINITE_REMAINDER_1_THROUGH_1999`. The tail ran FC2K, FW,
EW, NC, SC, GP, CF, WC, BCM, MC18 and the complete preserved LC theorem.
FC2K also executed its finite-target, prefix-family and central-completion
components. Its complete bounded-order arithmetic digest is

`b147b8bf7bb2286d99af6827786d906460d856ef0abb551c68314f7ecd05ac90`,

matching the separately reviewed independent arithmetic. The preserved
LC output SHA-256 remains
`8e70c0b49f720afacf735c59a0a14be95570be825c990597ddf01a33925d1df3`.

The finite command's complete output SHA-256 is
`887f8c53880e3b01e8bf3c24caca66083300fdbdeaeca63bf28f0583e9fbc34f`,
exactly matching its final independent review. Its report reproduces
every expected order and every aggregate, including 1,686,341 recorded
swaps and maximum observed line sum 68,630,847,793. Its rejection
controls include separate main-only-composite and anti-only-composite
fixtures. The independent finite prerequisite review additionally
reconstructed and verified the entire range with a separate exact
sieve and trial-division implementation.

### Observed installation-path diagnostic

The tail output in this export has SHA-256
`a5fa84880ea43fbbe55b3f95989e98f9dadbceaba34a1328d86523a4642e8b0c`,
whereas the tail review's earlier export records
`c0b35845a97d263ac2b41a277ec9c6bcdc823f4641c36474531cdc861f9d3bc0`.
I compared the actual reports. Their component summaries differ only
in FC2K's `finite_checks/source` diagnostic, 17604 versus 17588, and
its resulting complete-output hash. All mathematical summaries,
arithmetic digests, ratios, graph data and other component outputs agree.
Replacing just those two fields in the earlier full tail JSON reproduces
the exact new full-tail SHA-256.

This is the previously identified ancestor-depth counting diagnostic;
it is not a new numerical discrepancy. I record the actual output hashes
and difference instead of claiming that every full producer output is
byte-identical at arbitrary installation paths.

## 5. Independently written composition oracle

The separate review artifacts are:

| Artifact | SHA-256 |
| --- | --- |
| `reviews/sude-all-odd-independent-oracle.py` | `de206aff7f4d5d5a4acf54d332b9ecf5c490c0501a4c15c9cdb99536e05f5bca` |
| `reviews/sude-all-odd-independent-sources.json` | `04fbd627fc51bf44e932e2538cac44666a1c4546d9f0ccdb581ba37e1d672367` |
| Complete independent output with full-report checks | `0a383bc9fb5ce7174b651f8fe1edd92c6272e1353119f9cf74ba473e10866a9e` |

The oracle imports no producer or earlier reviewer module. Its source
map binds the 343 scientific files, its own executable identity and the
two actual final prerequisite reports. It requires no Git or private
artifact. An optional full-report input is generated by the public
default command, rather than being an inaccessible acceptance file.

The independent controls include:

- a separate AST audit of the exact source-set literals, two default
  component commands, absence of skip flags in those commands, and the
  distinct weaker `--composition-only` status;
- exact union and equality checks for every inherited source binding;
- a separate bounded raw-DEFLATE decode with header, trailer CRC,
  payload length and SHA-256 checks;
- a decoder written using little-endian byte slices, recovering all
  1,000 physical record headers, offsets, seeds, phase counts, lengths
  and record digests, and matching them to the accepted finite metadata;
- exact cell, line, swap and line-value totals, the order-one labels,
  and the algebraic finite/tail endpoint identities;
- rejection of incomplete order metadata, altered physical ranges,
  malformed and missing hash-map entries, false formal-proof flags,
  and success reports that omit a required full replay;
- direct black-box producer CLI controls: a valid weaker-mode positive
  run, followed by 24 malformed-manifest or physical-substitution
  rejections, including a truncated public gzip certificate.

The complete run passes **26,974 counted controls**, including 377
malformed-metadata rejections, 1,716 physical attacks covering every
scientific file, six physical-certificate range rejections, three
case-coverage rejections and five altered replay-report rejections.
The counts include parser and source-integrity assertions; they are not
a count of independently proved mathematical theorems.

I repeated this oracle in a separate fresh 347-file export containing
only the 343 scientific files, the two final prerequisite reports and
the oracle/map. Its output is byte-identical to the first independent
run. The no-Git default scientific run and the independent source checks
use only the canonical gzip certificate, not the earlier uncompressed
working file.

For reproduction from an exported problem directory with the review
bundle included:

```sh
python3 -B code/verify_sude_all_odd.py > all-odd-full.json
python3 -B reviews/sude-all-odd-independent-oracle.py --root . --full-report all-odd-full.json
```

Without `--full-report`, the independent oracle still checks the source
closure, physical finite range, mathematical case interface and rejection
controls, and explicitly reports that a full producer report was not
checked. Such a run must not be substituted for the two commands above.

The oracle does not independently repeat all 1.333 billion finite cells
or rederive every analytic/controller proof. Those are the explicitly
accepted prerequisites, independently checked in their own reports;
the full producer replay provides the additional current execution gate.
The new independent work here is the final source binding and case
composition. Universal coverage follows from the elementary integer
case argument and the accepted infinite theorem, not from the oracle's
finite sanity probes.

## 6. Imported claims, limitations and final status

The finite family is an exact computer-assisted finite proof: it
enumerates the specified prime pool, verifies a permutation, recomputes
all required sums and applies exact primality decisions. Discovery
screens are not acceptance tests.

The complete tail has conventional construction proofs, exact finite
inequality certificates and named imported classical analytic theorems.
The published BMOR finite computations are imported results, not zero
computations rerun by this project. The tail's reviewed primitive-character
normalization, omitted-prime-power payments and effective domains remain
unchanged. Historical quasi-RH files in the source closure do not select
an RH or quasi-RH assumption for this classical theorem.

The all-odd manuscript states these boundaries correctly and adds no
analytic hypothesis. A successful arithmetic script is not presented
as an independent proof of its analytic imports. Ordinary agent review,
formal kernel verification, external refereeing and publication status
remain distinct.

All 45 repository integrity tests passed after the review work. These
test repository integrity and tool behavior; they do not establish the
mathematical conclusion. No producer correction was requested for this
67647907 composition. The accepted scientific files and both prerequisite
source sets remain unchanged.

With the two final prerequisite acceptances, the independently checked
exhaustive case split, the complete source binding and the successful
fresh full default replay, the proposed all-positive-odd-order theorem
is accepted at the exact scientific revision stated in section 1.

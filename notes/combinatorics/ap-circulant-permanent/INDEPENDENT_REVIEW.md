# Independent automated review

Date: 2026-11-08. Review target: the exact file versions listed below.

**Outcome:** No unresolved mathematical or implementation defect was found in
the reviewed versions. The direct recurrence, its stated operation bounds,
and the explicit matching reduction and specialization are supported by the
invariant arguments and the finite exact checks described here. This finding
is scoped to the recorded versions and is not a proof-assistant certificate,
human-specialist review, external peer review, or certification of novelty.

This was a separate automated mathematical and code review, not authorship of
the public writeup. Its conclusions remain fallible. The reviewer did not
publish the package or assess repository permissions or publication mechanics.

## Mathematical checks

The review independently checked the following points.

- The identity `(j-i) mod n = j-i+n*1[j<i]` for `n >= 1`, the separate empty
  case, and the transpose convention give the stated circulant corollary.
- The four counters describe all processed endpoint colors and staircase
  matchings. All open staircase columns are eligible for every later row,
  with identical edge weight, so multiplying by their count is valid.
- Processing a row before its same-index column excludes diagonal staircase
  edges. Completed colorings require `h=0` and `r=c`; the two factorials count
  exactly their remaining bijections. Each expanded permutation term is
  counted once.
- The two pruning conditions are necessary completion conditions. They
  cannot discard a contribution to the answer.
- The proof is a polynomial identity over the integers, not an argument
  requiring positive weights, division, characteristic zero, or a domain.
  Integer multipliers and factorials use the ring's canonical integer map.
- Four bounded counters, constant transitions, and rolling layers give
  `O(n^5)` ring operations and `O(n^4)` stored ring elements. Precomputing
  integer scalars and factorials is consistent with this operation model.
- With integer input magnitudes below `2^L`, intermediate values have
  `O(n(L+log(n+1)))` bits. The stated conservative schoolbook time and storage
  bounds follow. For independently denominated rational inputs, clearing
  denominators can introduce `O(nL)`-bit integers; the final text correctly
  distinguishes this from the two-parameter AP case.
- The AP symbolic-degree argument gives `O(n)` coefficients per homogeneous
  state and the stated polynomial coefficient and bit bounds. It does not
  imply polynomial expanded output in all independent generalized variables.
- The five-vertex gadgets have exactly one external port in a perfect
  matching and the stated internal weights. The eleven-label expression
  generates precisely the required edges. Retiring the inactive label is
  safe. The bipartite balance equations leave four independent matching
  counts and the five transitions per gadget give the same asymptotic bound.

The strict-containment example is correctly restricted by using an integer
matrix of dimension two. The final explicit example is
`per(Circ(1,2,3)) = 54`.

## Exact execution checks

All executions below used Python 3.12.14 with bytecode writes disabled and
only the standard library. The reviewed source files were not changed by
these tests.

The package's reproducible suites were rerun successfully:

- `verify.py`: 1,311 counted instances, plus the explicit example and two
  input-validation checks. Its category counts and ranges agree with
  `VERIFICATION.md`.
- `check_gadget.py`: 90 graph-construction, exhaustive matching, and
  permutation comparisons.
- `check_profile.py`: 180 permutation comparisons, including 100 exhaustive
  gadget matching comparisons, with the balance assertions enabled.

These constitute 1,581 counted instances across the three scripts. They are
finite checks, not a proof for untested dimensions.

The reviewer also ran these additional checks against a column-subset
assignment DP, separate from the endpoint-color recurrence:

- 400 integer/rational instances with seed `3711826`: for each dimension
  `n=0,...,9`, 20 generalized instances and 20 AP instances. Alternating
  trials used signed integers or independently generated rational inputs.
  Integer numerators were drawn from `-20,...,20`; rational denominators
  were drawn from `1,...,19`.
- 336 instances with seed `180725` in the rings
  `(Z/mZ)[epsilon]/(epsilon^2)`, for `m=2,4,9`. For each modulus and dimension
  `n=0,...,6`, eight AP and eight generalized instances were evaluated using
  actual ring objects. Each element was represented by its constant and
  nilpotent coefficients, with exact ring addition and multiplication.
  These checks include nonzero nilpotents and zero divisors, rather than
  merely reducing an integer answer afterward.

The two additional campaigns were ad hoc review executions, not extra
packaged test scripts. Their counts should not be added to `verify.py`'s
reported total. The combined review execution count is 2,317 instances,
excluding repeated runs and validation-only calls.

The final documented CLI commands were also executed. They print `54` and
`-85175/972`, respectively. The signed-fraction command requires the documented
`--` argument separator.

## Literature and claim scope

The primary-source statement and unmatched-label invariant in
[Flarup and Lyaudet's journal manuscript](https://lyaudet.eu/laurent/Publi/Journaux/cliquepermTOCS.pdf)
support the main bounded-weighted-width comparison. The gadget and the
one-edge transitions are proved in this package; they are not attributed as
an AP theorem printed in that paper. The generic circuit-size estimate is
identified as loose, and the direct recurrence is not advertised as an
asymptotic improvement over the specialized matching framework.

The scopes of the other circulant comparisons and the
[OEIS numerical baseline](https://oeis.org/A086759) were checked against the
accessible primary sources. In particular, weighted circulants are explicitly
discussed in section 5.1 of Golin, Leung and Wang's
[expanded version](https://arxiv.org/html/0708.0907v1).

This was a bounded source check, not an exhaustive literature search. It
establishes neither priority nor absence of an equivalent or faster prior
algorithm. The package's express disclaimers of novelty, optimality, and a
new complexity-class result are appropriate. Generalized ring-object support
in the Python implementation requires arithmetic compatible with Python's
integer zero, one, and scalar multipliers.

GitHub visual rendering and remote publication were outside this review.
A source or claim change after the hashes below requires rechecking the
changed part before treating this report as applicable to it.

## Reviewed file fingerprints

SHA-256 fingerprints of the reviewed bytes:

```text
3175bba65ebc29b0847f34c87f047cfb6ec331ea48504115f29a7f94e05e5914  README.md
21dcee6aa131fad2d3fafdcfa7e10d8d53dd27b788980ecaeb034f777431b559  PRIOR_ART.md
cf8e38cafd6b2cca4b8b9f67b44e86dfce6256eb810ce99344b2ca8f9d2015e1  permanent.py
2cd0dfdf2005434c357cbd726b6a0b812ad9a408d730705841aa03175673e205  verify.py
930260cddb923a3e502cf280254c557c5efbc36419c3f3668c5cb1e49fba6b1a  check_gadget.py
5fc19baeb2976b4a34a442646c83bd48925d6ddeb605a9c5155c171e3b4be5c9  check_profile.py
de32bd0205f9a884e87d9f662ace4cc7614300429273f88b08726b125bcbf683  VERIFICATION.md
```

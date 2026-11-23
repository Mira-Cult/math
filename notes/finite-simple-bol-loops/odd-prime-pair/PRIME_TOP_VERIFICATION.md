# Verification of the prime-top two-type classification

**Mira Cult**

[Main proof and statement](manuscripts/0134-prime-top-two-types.md) · [Two explicit models](manuscripts/prime-top-construction.md) · [Odd two-prime order program](README.md)

The theorem concerns all finite simple proper left Bol loops at the specified orders, up to ordinary isomorphism. In particular it is not an enumeration of labeled stabilizers. Here are the mathematical and computational checks on which the account relies.

| Part | What was checked |
| --- | --- |
| Canonical envelope and outer architecture | Independent mathematical review checked the application of Foguel–Kinyon–Phillips to arbitrary finite simple proper loops of odd order, the full inverted mark class, ordinary core-freeness, the strict signed cuts, normal generation, the reciprocal Hall reduction, and the top bound. |
| Hall-fixed and Hall-moving cover | Independent review checked the actual row under Hall-fixed Frattini, the exceptional ternary and small-prime exclusions, the rank and sign costs, and the physical coverage of the first Hall-moving layer. |
| Construction and uniform isomorphism | Independent review checked the full transversal, core, generation, signed cuts and non-Moufang deduction, then the signed diagonal Hall alignment, true stabilizer lift, elimination of the internal axial brackets, and preservation of the square class. It separately replayed small-field coefficient cases and 250,000 constrained comparisons at $`p=5`$ for the two square classes. |
| The direct $`85{,}293`$ case | Independent review also checked the direct ternary proof. It replayed 354,294 ordered row products and 708,588 constrained conjugation traces across the normalized ternary parameters for the axial normal form. This is separate from the mathematical exhaustion of the other layers. |

The original checkpoints for the uniform census and its layer dependencies are `c9cdd1848eb34c576374614b19b65dcb38219480`, `3dbd527dcfcd5ac644127755e6ca238481cfbe19`, and `e13602d57beb50171bfbec921c71df7622b5ea45`. The public proofs do not require access to that research history. The public proof files contain the dependency closure, with accessible references to the previously published foundations. The outer reduction includes the canonical-coverage argument at `665f7356` and the reciprocal architecture at `74f78d87`, `5fdc0773`, and `8580e056`. The construction was checked at `c67ba2a9` and `34dfa9f6`; the direct order-85,293 theorem also uses `b615612e`, `124f4e5c`, `dd42a49d`, `2c6a6a41`, and `c00f51f6`.

## Reproduce the small-field checks

From this directory run the two Python 3 programs (standard library only):

```sh
python3 code/check_prime_top_first_hall_moving_rank_one.py
python3 code/check_prime_top_axial_bracket.py
```

The [rank-one coordinate check](code/check_prime_top_first_hall_moving_rank_one.py) tests row closure and the constrained first-axis conjugation equations used in the construction at $`p=3,q=13`$. The [bracket check](code/check_prime_top_axial_bracket.py) tests four Hall field examples for the rank of the linear internal-bracket conditions with and without the physical hyperplane condition. These programs supplement, rather than replace, the uniform proofs. They are not a formal verification of the theorem, a complete finite-table enumeration, or a journal peer review.

## Acknowledgment

Mira guided the classification strategy, with emphasis on matching the necessary structure of arbitrary loops to genuine constructions. OpenAI models assisted in developing and writing the proofs, implementing finite-coordinate checks, and carrying out separate proof reviews. No exact model version is inferred from a review label.

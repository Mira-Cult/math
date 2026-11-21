# The smallest square that holds 18 unit squares

**Mira Cult**

Let $`s(n)`$ be the least side of a square that contains $`n`$ unit squares with disjoint interiors. The unit squares may translate and rotate independently. Boundary contact is allowed.

**Theorem.** For eighteen squares, the optimum is

```math
s(18)=\frac{7+\sqrt 7}{2}=4.822875655532295\ldots .
```

This is an exact, computer-assisted optimality proof. [Hämäläinen’s earlier packing](https://erich-friedman.github.io/papers/squares/squares.html#2) already attained this side. The contribution is the matching **lower bound with no restriction on the orientations or contact pattern**.

![An exact packing of 18 unit squares. Six tilted squares are highlighted in blue; the other twelve are axis-parallel.](packing.svg)

## Why the proof needs two kinds of certificate

The [exact construction](replay/six-tilt18.json) uses twelve axis-parallel squares and six tilted ones. Its coordinates lie in $`\mathbb Q(\sqrt7)`$; the [construction checker](replay/six_tilt18.py) verifies every wall inequality and every pairwise separation without floating-point comparisons.

For the lower bound, a fixed set of 21 points inside a slightly larger rational test box gives every possible tile an interior point. The eighteen distinct points assigned to the tiles leave three unoccupied marks. Up to the eight symmetries of the box, there are 187 assignments of occupied marks to examine. Those assignments are discrete, but the positions and angles of their tiles still range over continuous sets.

For 181 of the 187 cases, exact bounds show that not even the slightly larger test box admits a packing in the case. In the remaining six, the proof allows branches that contain an optimal configuration. It finds specific tiles whose rows and separating faces force the *actual* enclosing side to be at least the claimed optimum. These branches prove an inequality instead of declaring their pose domains empty.

- [Proof and continuous-coverage details](proof.md)
- [Certificate map and replay commands](replay/README.md)
- [Verification and references](verification.md)

The theorem determines the optimal side length; it does not classify all configurations that attain it.

**Acknowledgment.** Mira Cult directed the research. OpenAI’s GPT-6.2 Astra developed the computer-assisted lower bound and exact construction. A separate OpenAI model review checked the mathematical assembly and reran the seven certificate groups.

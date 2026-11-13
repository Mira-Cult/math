# Integer-polynomial golfing

This work optimizes the length of a complete polynomial-generating program.
It shortens the description of a conditional Diophantine definition of the integers
over the rationals. It does not resolve the inherited arithmetic premises.

## Target and scope

For an integer polynomial `F` with one distinguished coordinate, the target is

```math
\{x\in\mathbb Q:\exists\mathbf y\in\mathbb Q^m,
F(x,\mathbf y)=0\}=\mathbb Z.
```

Every variable, including each witness, ranges over the rationals. The metric
is the complete generator's ASCII character count, including imports and data.
Variable count and expansion size may increase; the current generator also preserves total degree four. The ideal is 280
characters; a complete long-post-sized program is also useful. A download,
custom library import, unnamed polynomial, or truncated payload is not counted
as a self-contained solution.

**Arithmetic scope.** The construction inherits the premises explicitly stated
in the supplied JoseBrox source. These include elliptic group/height results,
the full normalized modular realization, pole obstruction and realization,
and simultaneous prime-pattern and approximation inputs. No new abc hypothesis
is added. The algebraic compression and finite coefficient checks do not
independently prove those deep inputs. See [source scope](source-scope.md).

## Complete generators

| Program | Complete ASCII characters | Output | Mathematical relationship |
|---|---:|---|---|
| [tweet_packed.py](code/tweet_packed.py) | **1,520** | A quartic in 3,779 variables, with input `x0` | Complete compressed program; prints exactly the reviewed polynomial. |
| [tweet.py](code/tweet.py) | **2,200** | The same quartic | Uncompressed golfing entry, using only Python built-ins. |
| [generate.py](code/generate.py) | 2,518 | The same quartic | Readable source pinned by the independent mathematical review. |
| [quartic262.py](code/quartic262.py) | 3,777 | Exact sparse coefficient dictionary `P`, with input coordinate 1 | Reconstructs the original 262-variable quartic at `A=149**19365`, coefficient for coefficient. |

All four programs contain all their mathematical constants. `tweet.py` and
`generate.py` need only Python's built-ins; the other two use only the standard
library. None accesses the network, external input data, or a repository-specific
library.
The entire program, not a helper importing this directory, is the golfing entry.

The first three programs print the identical polynomial expression in variables
`x0,x1,...`. [Representation and output identity](representation.md) records the
packing format and the exact relation to the reviewed source; the
[representation review](reviews/representation.md) independently checks both
short forms at commit `ea067402e7010fcc1d57a1c10e0d7e3dd584e8de`.
Fixed integer powers in its output are coefficients. Every division in the
construction has already been replaced by a polynomial equation for an inverse.
Thus the generated expression itself contains only integer constants, variables,
addition, subtraction, multiplication and nonnegative integer powers.
Its 3,751 residual equations are quadratic or linear, so their sum of squares
has degree four. The output has 99,396 ASCII characters without the final newline.

The exact quartic's dictionary maps a sorted tuple of coordinate indices to its
integer coefficient. For example, `(1,1,4)` denotes `x1**2*x4`; `()` denotes
the constant monomial. It has 3,494 nonzero terms, degree four, and 262 total
coordinates. Its maximum coefficient is `149**38730+1`.

## Why the description gets shorter

The source optimizes variable count and total degree. This project instead
uses ordinary elliptic addition and doubling, coordinate pairs for
`Q(sqrt(2))`, and a generic compiler for rational arithmetic. Each arithmetic
operation may introduce another variable, but its implementation is shared.

A further mathematical simplification replaces four specially packed local
factors by two uniform products:

```math
 W=\prod_{f\in\mathcal F}(1+q^3f^2)
       \prod_{c\in\mathcal C}(1+q^5c^2).
```

The ten reciprocal-abscissa tests in `F` and six comparison tests in `C` are
defined in [the replacement proof](uniform-factors.md). The complete
[compiler and arithmetic transfer proof](proof.md) specifies the resulting
polynomial and both directions of its conditional integer-detection theorem. Parity of valuations
separates the constant and nonconstant term in every factor. The resulting
bounds supply all the source's required local precision. The source's
simultaneous completeness construction also satisfies these factors, with the
same explicit parameter `N=9682`.

## Reproduction

Python 3.11 or newer is sufficient. From this directory:

```sh
python code/tweet_packed.py > /tmp/integer-polynomial.txt
python -c "import runpy; p=runpy.run_path('code/quartic262.py')['P']; print(len(p),max(map(len,p)))"
```

The second command prints `3494 4`. Additional checks are:

```sh
python code/check_tweet.py
python code/check_compiler.py code/generate.py
python code/check_circuit_values.py
python code/check_quartic.py code/quartic262.py /path/to/pinned-upstream-clone
```

The last check reads only the two upstream JSON coefficient tables and verifies
their SHA-256 hashes before comparing all rows and coefficients. The two
generators themselves have no such external-data dependency.

 Importing `generate.py` through `runpy`
instead of executing it retrieves the expression as `polynomial`, the residual
list as `E`, and the number of coordinates as `n` without printing the expression.

The finite checks concern exact algebraic construction and source equivalence;
they cannot establish the infinite arithmetic projection by sampling rational
inputs. The [independent construction review](reviews/construction.md) accepts the
conditional arithmetic proof at source commit
`1dc330d814a5e57bbd11d93bbb77fd02094bd062`. The separate
[compiler and coefficient review](reviews/compiler-and-coefficients.md) states
its narrower scope and authorship exclusions. [Publication verification](VERIFICATION.md)
records the commands, results and remaining boundaries.

## Sources and attribution

- JUVa (the JoseBrox repository), *Polynomial presentations of the integers over the rationals*,
  [source repository at `fa09c9c6c97982c13265e7088d95cdb61b3e90cf`](https://github.com/JoseBrox/diophantine-z-q_improvements/tree/fa09c9c6c97982c13265e7088d95cdb61b3e90cf).
- The same revision, [*An explicit defining quartic in 262 variables*](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/fa09c9c6c97982c13265e7088d95cdb61b3e90cf/papers/quartic/quartic262_20261110_v21.tex),
  Theorem 1.1 and sections 4–9 (scalar certificate through completeness).
- The coefficient data used in `quartic262.py` are the same revision's
  `computation/quartic/family262_v21/quadratic-family262-v21.json` and
  `polynomial-family262-v21.json`, originally licensed under
  [CC BY 4.0](https://github.com/JoseBrox/diophantine-z-q_improvements/blob/fa09c9c6c97982c13265e7088d95cdb61b3e90cf/LICENSE).
  The compressed representation is an adaptation of that data. Source notices
  and underlying Glazer/Sun provenance are retained by reference.

The golfing programs and uniform-product modification were developed by the
ChatGPT Astra research team for Mira. This is not a novelty or optimality claim
for the original integer-defining construction.

## Copying the program into a post

The 1,520-byte entry is already a single physical line (plus its terminal newline).
Visual wrapping is harmless; inserted newlines inside its quoted payload are not.
Use [the paste-friendly version](code/tweet_wrapped.py) when hard line breaks are
unavoidable: it strips whitespace inside the triple-quoted payload before decoding.
That version is **1,559 ASCII bytes**, not the 1,520-byte golf entry. Do not insert
breaks inside Python keywords or identifiers, alter punctuation, or use smart quotes.
Both versions execute an embedded program: inspect the readable source before running.

[Provenance and attribution](PROVENANCE.md) and [publication checks](VERIFICATION.md)
state the exact release scope. No formal verification or external referee acceptance
is claimed.

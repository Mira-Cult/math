# References and mathematical dependencies

## Analytic inputs

- Wataru Kai, *Notes on Mitsui's Prime Number Theorem with Siegel zeros*,
  [arXiv:2209.11816v3](https://arxiv.org/abs/2209.11816v3), Theorem 3.1.1.
  The proof retains both the enclosing-radius error and possible exceptional term.
- Wataru Kai, *Linear patterns of prime elements in number fields*,
  [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5), Theorem 12.1.
  The application uses three forms in four integer variables, with the stated
  coefficient and local-factor uniformity; it does not apply a fixed-system
  theorem directly to a growing array of forms.
- Bingrong Huang, Jianya Liu, and Zeév Rudnick, *Gaussian primes in almost all
  narrow sectors*, [arXiv:1903.04005v1](https://arxiv.org/abs/1903.04005v1).
  Discussed for scope comparison, not used as a uniform adaptive-box guarantee.

The [analytic manuscript](manuscripts/analytic_inputs.md) supplies the exact
hypotheses, error comparison, exceptional-zero treatment, and target construction.
Its Siegel step leaves the threshold ineffective.

## Public ordinary-prime dependencies

The mathematical imports are available publicly in this repository:

- [Full signed-line cube composition](../sudes-first-conjecture/prime-cube.md).
- [Signed integer incidence](../sudes-first-conjecture/cube/signed_incidence.md).
- [Signed physical trades](../sudes-first-conjecture/cube/signed_trades.md).
- [Axis controller](../sudes-first-conjecture/cube/cube_controller.md).
- [Tensor incidence and bounded coefficients](../sudes-first-conjecture/cube/incidence.md).
- [Compatible cube targets](../sudes-first-conjecture/cube/cube_targets.md) and
  [signed targets](../sudes-first-conjecture/cube/signed_targets.md).
- [Square finite controller](../sudes-first-conjecture/explicit-controller.md)
  and [exact-total targets](../sudes-first-conjecture/explicit-targets.md).
- [Degree-64 graph and expansion-eight construction](../sudes-first-conjecture/controller.md#f-independent-row-and-column-controls).

Only the specified geometric and integer-flow interfaces transfer to the
quadratic-ring controller. Ordinary rational-prime supplies and scalar
subset-sum conclusions are not silently reused as rank-two statements.
The [architecture audit](manuscripts/ordinary_architecture.md) explains this boundary.

[Provenance](PROVENANCE.md) identifies the research snapshots and public source map.
No exhaustive-literature or priority claim is made.

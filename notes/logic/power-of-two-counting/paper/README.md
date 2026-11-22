# Power-of-two counting captures uniform TC⁰

*Mira · November 2026*

[Read the paper (PDF)](power-of-two-counting.pdf) · [LaTeX source](power-of-two-counting.tex) · [Research writeup](../README.md)

The paper gives the exact finite-order interpretation of multiplication, the uniform circuit-class consequence, and the lower bound excluding counting depth one. Depth two remains open.

## Build

From this directory, run twice with a standard TeX Live installation:

```sh
mkdir -p build
pdflatex -no-shell-escape -halt-on-error -output-directory=build power-of-two-counting.tex
pdflatex -no-shell-escape -halt-on-error -output-directory=build power-of-two-counting.tex
```

The document has no external figures, data files, or bibliography build step.

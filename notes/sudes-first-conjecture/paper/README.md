# Sude's prime-sum squares

*Mira · 12 November 2026*

- [Read the paper (PDF)](sude-prime-sum-squares.pdf)
- [LaTeX source](sude-prime-sum-squares.tex)
- [Research writeup and construction source](../research-writeup.md)

The paper follows a hypothetical square through prime-target selection,
reserved pair and rectangle swaps, completion of one reference arrangement,
integer-flow routing, and simultaneous diagonal repair. It proves the
expository combinatorial steps and explicitly cites the quantitative
prime-supply and joint-placement results. Exact certificates supply the
1,000 positive odd orders below 2000.

The finite certificate assertion and fifteen named analytic statements remain
explicit inputs. Publishing this exposition does not change the verification
scope recorded in the research writeup.

## Build the paper

The published 13-page PDF was compiled from the accompanying, unchanged LaTeX
source with Tectonic using cached resources. With Tectonic installed, run:

```sh
mkdir -p .build
tectonic --untrusted --keep-logs --outdir .build sude-prime-sum-squares.tex
```

The source includes its bibliography and has no separate image dependencies.
The [SHA-256 checksums](SHA256SUMS) identify the published source and PDF;
compilation metadata can differ in a fresh build.

The paper's construction-source citation is pinned to public revision
`d16fd1ee2dd6f8440c6c47b1b7575d0fca8b4241`. The
[current research writeup](../research-writeup.md) includes GitHub rendering
corrections without changing its mathematical statements or verification claims.

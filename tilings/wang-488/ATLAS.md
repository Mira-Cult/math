# Reproduce the exact tile atlas

`488-wang-tiles.svg` shows all **488 actual oriented tiles exactly once**.
It is a tile inventory, not a valid tiling. Its seeded-half-plane scope is
not an unrestricted whole-plane result. The original zero-based index is
printed at each center. Seed tile 487 is enlarged and outlined in gold;
it is not duplicated.

With Python 3, Inkscape, and DejaVu Sans / DejaVu Sans Mono installed:

```sh
python render_atlas.py
```

This regenerates the SVG and a 3600 × 4500 PNG for sharing. The generated
PNG is not needed in the source repository. Use `--svg-only` to regenerate
the SVG, palette, and verification report without Inkscape.

The renderer reads the existing `k215_diagonal_488.tsv` in this directory.
It requires SHA-256
`371ebc4063c47ba3491d99c6884faa43633d3ea2600411d9eee9b4a020207017`,
then checks 488 distinct tuples, 221 edge colors, exact indices, and the
sole seed. It parses the generated SVG back to verify all tile indices,
edge identities, and colors against the TSV. `atlas-verification.json`
records these checks; they are not a substitute for the mathematical proof.

The public TSV URL is retained in the SVG metadata. Research provenance
is separately recorded by source commit
`cebfe3e282ee65337d9fa69c274d5321d757e340`. Reproduction needs no access to
the research repository.

## Edge codes

Hue alone cannot reliably distinguish 221 colors. The exact printed edge
codes are authoritative; `palette.json` gives the full source/color map.

| Display code | TSV edge identity |
| --- | --- |
| Hn | `head:n`, with the displayed decimal state number n |
| 0, 1 | `sym:0`, `sym:1` |
| B | `bottom` |
| R | `init:R` |
| W | `wall` |
| WS | `wall:start` |

The SVG retains each full source edge name in machine-readable attributes
and descriptive tile titles. No tile is rotated or reflected. All triangle
labels have a text/background contrast ratio of at least 4.74:1. The full
atlas and a native-resolution detail were visually inspected for overlap
and readability. The public SVG was rendered again and checked to be
pixel-for-pixel identical to the reviewed shareable PNG.

The headline 975 → 488 compares tile-type counts for the earlier K230
seeded construction and this K215 diagonal construction. It does not
describe a Turing-machine state-count reduction.

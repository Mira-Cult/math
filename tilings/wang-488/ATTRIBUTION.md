# Attribution and license status

## The 975-tile starting point

The comparison construction is Conor Grogan, with Claude (Anthropic),
[*975 Wang tiles whose seeded tiling is equivalent to Con(ZFC)*](https://github.com/jconorgrogan/k230-wang-tiles/tree/1e483bad46dd91d9ad20aa38b7f750986be043fc),
pinned to commit `1e483bad46dd91d9ad20aa38b7f750986be043fc`.
Its target is a seeded half-plane, as is the 488-tile result here.
The action/merge comparison implemented in `tm_to_wang.py` follows that
construction. The diagonal encoding replaces its simulation geometry;
the upstream compiler proof does not automatically certify the replacement.

The K230 transition table is from
[Elliot Glazer's `k230-rocq`](https://github.com/elliotglazer/k230-rocq/tree/a8312f0ca703bc81baac16695a437a7d3788f690),
commit `a8312f0ca703bc81baac16695a437a7d3788f690`.

## The exact K215 machine

The primary K215 table and its ordinary mathematical and external
Lean/Rocq calibration are from
[Vladimir Reshetnikov's `ProveIt`](https://github.com/VladimirReshetnikov/ProveIt/tree/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/candidate-k215),
commit `440dd03ab8de73ba5ea5218c37527a6edb7e5d8b`.
This is the exact primary 215-working-state dense table, not another
same-sized candidate. [SOURCES.md](SOURCES.md) identifies the proof
endpoints and their verification limits.

Neither raw upstream machine table is vendored here. `sources.json`
records their exact commits, paths, download URLs and SHA-256 values;
`fetch_sources.py` retrieves them from their publishers and verifies
those hashes. No third-party source is relicensed by this release.

## Diagonal computation

The general idea of using diagonal spacetime is older. Emmanuel Jeandel
and Pascal Vanier, [*Π⁰₁ sets and tilings* (2011), §3](https://arxiv.org/html/1102.1189v2#S3),
use northeast time and northwest-to-southeast tape diagonals in a different
construction. Their work is a precedent, not a proof of this exact compiler
or its count. No historical priority is asserted here.

## This release

The diagonal compiler, finite-window invariant, exact tile/certificate data,
and research proof were prepared in `Mira-Cult/turing-machines`, commit
`cebfe3e282ee65337d9fa69c274d5321d757e340`, directory `research/wang/`.
That repository is private. The public article, source pins and reproduction
code here are self-contained. `SOURCE.json` records preserved file hashes
and the limited public-facing adaptations. `independent_check.py` is an
additional independent finite audit prepared for this release; it imports
neither the compiler nor the certificate checker.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner. This notice does not alter any upstream license or
grant rights to third-party source material.

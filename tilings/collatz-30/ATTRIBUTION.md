# Attribution and license status

## This construction

The exact 30-polygon construction, arithmetic, frame, geometric compiler,
ordinary mathematical proofs and finite checkers were prepared in
`Mira-Cult/math-wip`, directory `problems/collatz-polygons/`, scientific commit
`3a73ade5ef934e2f073b3a2d95156c5571d2011d`.
That research repository is private; this public package is self-contained.
[SOURCE.json](SOURCE.json) records hashes of the preserved sources and the
limited public-facing edits. Existing source author statements, including
statements identifying task-agent authorship, are retained. Internal task-agent
review is not external human expert review or proof-assistant verification.

## Background and prior constructions

The source reference list attributes the Golomb-style corner carrier to
Jed Chang-Chun Yang, *Computational Complexity and Decidability of Tileability*,
UCLA dissertation (2013), Figure 2.3 and printed pages 13–14
([author PDF](https://mathcs.bethel.edu/yang/papers/yang-thesis.pdf)).
The integer reconstruction, width profiles, exhaustive local witnesses and
converse for the actual fourteen-side family are supplied here; no external
compiler theorem silently certifies this modified family.

Related arithmetic constructions include Matthew Cook, Tristan Stérin and
Damien Woods, *Small Tile Sets That Compute While Solving Mazes*, DNA 27 (2021),
Appendix A and Figure 7 ([paper](https://doi.org/10.4230/LIPIcs.DNA.27.8)), and
Tristan Stérin and Damien Woods, *The Collatz Process Embeds a Base Conversion
Algorithm* ([paper](https://arxiv.org/abs/2007.06979)). These are background,
not proofs of the recurrent whole-plane polygon theorem stated here.

The earlier [17-state beeping-machine release](../../turing-machines/collatz/beeping17/README.md)
is a different reduction and is not a build or proof dependency of this package.
Its upstream attribution and license notice remain in
[the Turing-machine attribution file](../../turing-machines/ATTRIBUTION.md).
No source from those upstream machines is copied into this package.

## License choice

No repository-wide license has been selected. Public availability is not an
additional license grant. A root license choice remains with the repository
owner. This notice does not alter upstream licenses or relicense third-party
source material.

# Attribution and license status

The [17-state construction](README.md) is released from
`Mira-Cult/turing-machines`, commit
`116c88e23fb6580113b1f86f22816bdce316ba1f`, directory
`experiments/collatz-beeping17/`. Its exact table and two validation programs
are preserved in the public packet, with hashes in
[SOURCE.json](SOURCE.json). The source repository is private;
the public proof and checks are self-contained.

Its arithmetic core is adapted from Charlie Reams's 14-state weak-Collatz
machine in [calr3/tinycryptids](https://github.com/calr3/tinycryptids/tree/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz),
pinned to commit `ad9c597ad728f301400325b8e2115a4bb62a25d3`.
The upstream [README](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/README.md)
and [generator](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/build.py)
explicitly derive that 14-state design from the earlier 16-state release
[documented in this family](../cycle16/README.md). The 17-state machine removes the bounded search's equality
and overflow handling, and adds a six-state input-counter increment and copy
routine. No upstream source files are vendored here.

Neither the upstream Lean theorem nor this repository's proofs for the other
two tables certify the 17-state table. The new article proves that table directly
in ordinary mathematics; no proof-assistant certificate is claimed.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner; no third-party source is relicensed by this notice.

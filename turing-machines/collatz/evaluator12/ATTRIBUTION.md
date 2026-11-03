# Attribution and license status

The construction originates in Pascal Michel, *Simulation of the Collatz
3x+1 function by Turing machines*, §5.4, machine M8 (13 states, 2 symbols),
[arXiv:1409.7322v1](https://arxiv.org/abs/1409.7322v1).
The released 12-state table removes a redundant state on the valid-input
return path. The Lean proof checks the exact released table directly; it
does not assume that the state reduction preserves behavior.

## Shared arithmetic proof

The common arithmetic proof has the Reams attribution recorded in the
[family attribution](../ATTRIBUTION.md#sixteen-state-cycle-detector-and-arithmetic-proof).
The exact machine is checked directly, not certified by an upstream theorem.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner; no third-party source is relicensed by this notice.

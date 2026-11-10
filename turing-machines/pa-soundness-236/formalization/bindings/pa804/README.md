# PA804 successor binding

PA804 is the next physical target for the theory lane. PA926 remains the frozen
integration reference for the published Lean source. The arithmetic priority is
unchanged: finish the genuine PA/K finite-proof interpretation, then compose it
with implementation refinements for either physical table.

## Exact recovery

The selected literal [machine.tm](machine.tm) has 804 states and 1,608 binary
rows, SHA-256
`ba5ecf486757f55aa872d1a10fc5360cbed2070cde2d975fa2ee1c54fc536df8`.
State zero, head zero and blank zero are initial. BIT0 is emitted on exit from
state 174 reading one; BIT1 is emitted on exit from state 175 reading one.
All other rows are silent. These labels differ from PA926's 198/199 labels.
The selected bootstrapped table must not be confused with this successor's
926-state counted-initializer control, whose SHA-256 starts `4412d703` and
which is distinct from the frozen PA926 table.

The source is the recovered `pa804_checkpoint.zip`, 234,667 bytes, SHA-256
`b1cb4f1fdbcc5e183a049c2e57adcfa1b28df80e91c0962301b6f1388601f9e9`.
Its 41-file content manifest was verified. The archive reported no published
producer/delivery commit, and PR54 was independently observed at
`266a3116fd8662ce118051ee1e85616cf3200947` when recovered. Accordingly,
[origin.json](origin.json) identifies archive bytes rather than inventing a
compressor commit. This directory publishes a theory-lane reference copy; it
does not change the compressor's branch or assert its review is complete.

The ten selected build inputs, their vendor license, selected table/metadata,
and separate finite checker with its one-stack parent input are retained as
exact recovered bytes. [input-manifest.json](input-manifest.json) pins the
build inputs; [origin.json](origin.json) maps all sixteen retained source/data
files to their archive paths and hashes. The original archive's raw logs,
binary recovery ZIP, unrelated variants' outputs and large physical witness
are not dependencies of this reference copy.

## Reuse and obligations

The [reference producer](baseline/code/compact/source.py) is byte-identical to
[the pinned PA926 producer](../pa926/producer.py). The selected
`ReassociatedOneStack` class inherits `OneStack`, then `Streaming`, then the
same compact `Direct` implementation. It keeps the K axiom constructors,
postfix commands, named-variable convention, proof-code enumeration and
addressed unary observer. The `Canonical` variant changes admission and is
explicitly **not** selected. No PA208 transfer is part of this build.

The implementation changes streaming field emission, shared named lookup,
register reuse, one-stack matrix evaluation, grammar factoring and eight
reassociations. Inspection and finite graph checks support the intended same
record function; a Lean equivalence for those changes is still required.
The exact formal boundary and local obligations are in
[implementation-refinement.md](../../implementation-refinement.md#pa804-successor-target).
No new observer vocabulary or arithmetic foundation is needed to state them.

## Reproduction and evidence scope

From the repository root, using Python 3 and its standard library:

```sh
python -B problems/pa-soundness-lean/code/verify_pa804.py
python -B problems/pa-soundness-lean/bindings/pa804/build_selected.py \
  --out /tmp/pa804-reference-rebuild
python -B problems/pa-soundness-lean/bindings/pa804/verify.py \
  --build /tmp/pa804-reference-rebuild \
  --parent problems/pa-soundness-lean/bindings/pa804/one-stack-parent-metadata.json
cmp /tmp/pa804-reference-rebuild/machine/boot/quotient/machine.tm \
  problems/pa-soundness-lean/bindings/pa804/machine.tm
```

Use a fresh output directory. The recovered separate checker was run on the
original archive inputs and checked 3,464 raw rows, 4,970 primitive occurrences,
and 6,517 control edges, including both decrement outcomes. These are finite
Python checks. They neither prove the source-stage invariant nor instantiate a
Lean `ImplementationCertificate`. The archive's reported 66,826,399-transition
dual simulation is historical evidence and was not rerun for this binding.

A fresh rebuild from the retained source closure also completed. All eleven
generated selected files (the four tables and their metadata, ledger, input
manifest and graph certificate) were byte-identical to the archive, and the
separate checker passed again against the rebuilt artifacts. The original
six-binding audit and the new successor identity/row audit both passed.

The binding update changes no Lean declaration, axiom audit, dependency pin,
normalizer, observer formula or selected PA926 input. The successful Lean build
and kernel replay remain those recorded at the frozen mathematical source in
[CONTINUATION.md](../../CONTINUATION.md); this update does not claim a new replay.

## Frozen source and independent compatibility review

The binding source is commit
`be10f24a7e95a4a69f05aeddddcc442792216586`, tree
`3d7102a7f17445ff65ee4d13e955e99bad1d76c5`.
The [independent compatibility review](../../proofs/pa804-compatibility-review.md)
binds its input, definition and finite-check findings to that revision. It found
no blocker within that scope; it does not certify the open PA/K or physical
proofs. The source's [remote integrity run](https://github.com/Mira-Cult/math-wip/actions/runs/41179717697)
completed **skipped**, not passed. Later delivery CI status is recorded in PR60.

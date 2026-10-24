# K215 source and proof provenance

## Exact transition table

- Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
- Read-only source pin: `440dd03ab8de73ba5ea5218c37527a6edb7e5d8b`.
- [Dense table](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm).
- Table SHA-256: `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
- Format: `state read write direction next`, start state 0, symbols 0 and 1,
  all-zero two-way infinite tape, 215 working states 0 through 214, separate
  halt state 215. All 430 state/read rows are explicitly present. Initialization
  is included in the 215 count. Exactly one row targets halt: `68 1 1 R 215`.
- The supplied `fetch_sources.py` downloads this table at the pinned commit
  and rejects any bytes with a different SHA-256. The raw table is not
  redistributed in this release.

## Mathematical claim and proof-assistant endpoints

The [machine README](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md)
states the ordinary mathematical result

```
ZFC proves: not Halt(K215, blank) iff Con(ZFC).
```

The [ordinary proof](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md)
explains the source transformation, complete guarded control-flow agreement,
local tape blocks, quantified runtime, and exact blank initialization. Its
consistency calibration is inherited from the dominated numerical calculus.

The [literal Lean endpoint](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean)
has the following type:

```
SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot
```

The negated theorem `nonhalting_iff_zfc_consistency` is derived by
`not_congr`. The [dense machine definition](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDense215.lean)
lists all 215 rows and checks its relabeling to the sparse implementation.

The [formal verification record](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md)
reports original full builds recorded at `613f9cf28a`: 204 project Lean modules
and two endpoint clients; 237 Rocq sources and recursive `coqchk`. The current
Lean simplification checkpoint has a smaller dependency closure, separately
bound by its retained phase-15 records. The transition table and endpoint
statements remain unchanged.

The raw [Lean endpoint audit log](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/actual/audit/independent/compiler.log)
lists only `propext`, `Classical.choice`, and `Quot.sound` for each endpoint.
The raw [Rocq dense endpoint log](https://github.com/VladimirReshetnikov/ProveIt/blob/440dd03ab8de73ba5ea5218c37527a6edb7e5d8b/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/rocq/actual/K215F.CorrectDense215.log)
prints `Closed under the global context` twice. These logs and the literal
Lean endpoint were inspected in the source research packet; the whole proof
closure was **not rebuilt for this release**.

## Scope qualifications

1. The external Lean/Rocq theorems do not assume consistency and do not assert
   unconditional nonhalting. They identify finite halting with finite ZFC
   refutation.
2. The verification record explicitly says that this is not an internal PA
   endpoint and not a derivation already encoded in ZFC's own proof syntax.
   The ordinary exposition asserts formalizability in ZFC. Do not describe
   the external theorem as an already kernel-checked internal ZFC proof.
3. Same-size alternative 215-state tables in the repository do not silently
   inherit these exact-byte endpoints. This investigation uses the primary
   dense table only.
4. A tile compiler must prove its own simulation equivalence. None of the
   upstream machine proofs certifies a tile conversion automatically.
5. Seeded half-plane tiling and unrestricted full-plane tiling are different
   assertions. The small tile constructions investigated here have trivial
   periodic full-plane tilings if their seed condition is omitted.

## Tile-relevant independent counts

| Quantity | K215 |
| --- | ---: |
| Transition rows | 430 |
| Nonhalting-target transition rows | 429 |
| Distinct full action payloads `(target,write,direction)` | 297 |
| Distinct nonhalting full action payloads | 296 |
| Distinct incoming `(target,direction)` including halt | 244 |
| Distinct nonhalting incoming pairs | 243 |
| Nonhalting L target states | 45 |
| Nonhalting R target states | 198 |
| Nonhalting L transition rows | 82 |
| Nonhalting R transition rows | 347 |

Finite-state Mealy refinement of the literal two-symbol control table, with
halt distinguished and write/motion labels preserved, stabilized at 216
classes including halt. Thus ordinary control-state bisimulation alone gives
no further state merging for this table.

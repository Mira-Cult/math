# Optional direct scalar half

The only new source pattern is an augmented assignment `x //= 2`, with a
named target and literal integer two. Its natural-language meaning reads x
once and replaces that same source cell by its quotient. No operand effect,
temporary result, or second destination must be retained.

The native half/parity primitive already replaces x by `floor(x/2)` and
leaves every other register unchanged. Place it as the left child of the
binary pair `(native_half(x), _break.0)`. For odd input its successful return
selects the right child; that finite ordinary return reaches the continuation
outside the pair. For even input its failed return skips the right child and
reaches that same continuation directly. Thus both possible parities have
the same quotient and next source operation. Neither branch emits an event
or executes an infinite administrative loop. The surrounding pair supplies
the extra zero edge required by the conditional native ABI; deleting it
without a separate control proof would be invalid.

The original source CFG and its liveness/interference construction are
unchanged. The target's new value is defined in its own allocated source
cell. Any distinct source cell live through this augmented assignment is
kept distinct by the existing definition/live-out interference rule.
Compiler-owned micro and scratch cells are not touched. No destructive
delayed argument or earlier source read is introduced.

`scalar_half.py` keeps each exact three-statement unary-record block together
before forwarding it to the inherited native record matcher. In particular,
it does not accidentally split off the decoder's final `stream //= 2` and
lose that block's established semantics or sharing. Unsupported statements
use the inherited lowering.

The native tag remains present for source-CFG name mapping, true half/parity
abstract transfer, no-search certificate replay, optional finite-control
rewriting, bank projection and physical generation. The two-outcome control
graph check explicitly verifies any later contraction. The native primitive
terminates for every natural input; the extra parity-discard return is
finite. Consequently source values, ordered events and cofinal progress are
preserved. Full physical counts are obtained only by `build_scalar.py`.
This optional extension does not edit the frozen 446-state producer or the
previous native kernel/selector files.

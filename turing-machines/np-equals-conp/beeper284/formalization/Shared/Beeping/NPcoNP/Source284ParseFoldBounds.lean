import Shared.Beeping.NPcoNP.Source284ParseBounds
import Shared.Beeping.NPcoNP.Source284ParseFoldStep

/-! The exact two-flag marker/payload step satisfies the generic finite-prefix
size hypothesis needed for its canonical TM2 fold.  The parser's source-level
meaning and the polynomial-time fold construction are separate results. -/

namespace Shared.Beeping.NPcoNP.Source284ParseFoldBounds

open Shared.Beeping.NPcoNP.Source284ParseFoldStep
open Shared.ComplexityBridge.TM2PolynomialFold

/-- Processing one input bit adds at most one payload cell. -/
theorem step_acc_length (s : Packed) (b : Bool) :
    (step (s,b)).2.length ≤ s.2.length + 1 := by
  rcases s with ⟨⟨d,p⟩,xs⟩
  cases d <;> cases p <;> cases b <;>
    simp [step, state, done, pending, consume, mark, stop, bit, acc]

/-- Every prefix of the input has encoded fold-state size no greater than
the canonical encoding of the complete input and initial Boolean flags. -/
theorem prefix_encoded_bound (flags : Bool × Bool) (xs pref tail : List Bool)
    (hxs : xs = pref ++ tail) :
    (BitstringEncoding.bitEncode (fold step (flags,[]) pref)).length ≤
      (BitstringEncoding.bitEncode (flags,xs)).length :=
  Source284ParseBounds.fold_prefix_encoded_bound step step_acc_length flags xs pref tail hxs

end Shared.Beeping.NPcoNP.Source284ParseFoldBounds

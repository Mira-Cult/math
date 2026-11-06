import Shared.Beeping.NPcoNP.Source284GuardedBitsTM2
import Shared.Beeping.NPcoNP.Source284LinearPaddingTM2

/-! Construct the actual source frame of the bounded serialized guarded
loader. Both cutoff and source code are literal bit lists, and padding is
computed from their actual lengths; no canonical numeral expansion is used. -/
namespace Shared.Beeping.NPcoNP.Source284GuardedFrameTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284GuardedBitsTM2

/-- `p = (input bits, (unary cutoff, original finite row list))`. -/
def frame (p : Input) : List Bool :=
  Source284LinearPaddingTM2.frame (bits p,p.1,p.2.1)

theorem frame_isPolyTime : IsPolyTime frame := by
  let pub : Input → List Bool := fun p => p.1
  let tail : Input → List Bool × Shared.Beeping.NPcoNP.Source284EncodedRows.EncRows := fun p => p.2
  let cutoff : Input → List Bool := fun p => (tail p).1
  let params : Input → List Bool × List Bool := fun p => (pub p,cutoff p)
  have hp : IsPolyTime pub := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tail := TM2GuardAllStep.second_isPolyTime
  have hc : IsPolyTime cutoff := TM2Compose.isPolyTime_comp tail
    (fun p : List Bool × Shared.Beeping.NPcoNP.Source284EncodedRows.EncRows => p.1)
    ht TM2PairFirst.first_isPolyTime
  have hpar : IsPolyTime params := TM2GuardAllStep.pair_isPolyTime pub cutoff hp hc
  have hargs := TM2GuardAllStep.pair_isPolyTime bits params bits_isPolyTime hpar
  have h := TM2Compose.isPolyTime_comp (fun p : Input => (bits p,params p))
    Source284LinearPaddingTM2.frame hargs Source284LinearPaddingTM2.frame_isPolyTime
  change IsPolyTime (fun p : Input => Source284LinearPaddingTM2.frame (bits p,p.1,p.2.1))
  simpa [params,pub,cutoff,tail] using h

end Shared.Beeping.NPcoNP.Source284GuardedFrameTM2

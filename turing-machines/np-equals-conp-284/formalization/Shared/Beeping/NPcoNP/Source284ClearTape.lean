import Shared.Beeping.NPcoNP.Source284ClearExit
import Shared.Beeping.NPcoNP.Source284SerializerTrace

/-! The two-row clearing exit creates the physical boundary required by the
later reflected untagger. This theorem is a tape-layout identity, independent
of the choice of continuation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearTape

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284ClearExit (cleared)

/-- Overwrite the scanned cell and its physical predecessor with zero;
all other cells are unchanged. -/
def clearBoundary (t : Tape) : Tape := (false::t.1.tail,false,t.2.2)

/-- The numeric exit always lands in forward orientation and represents the
same two cleared physical cells, regardless of the incoming orientation. -/
theorem cleared_logical (t : Tape) (rev : Bool) :
    cleared (Nat.pair (Source284JoinedEndDetectorTable.index .done)
        (Source284FiniteRelativeRows.index 0 rev)) (lifted .done (logical t rev 0)) =
      logical (clearBoundary t) false 0 := by
  rcases t with ⟨left,head,right⟩
  cases rev <;> cases head <;> cases left <;>
    simp [cleared,Source284OrientedExit.side,Source284FiniteRelativeRows.index,
      Source284CompileRecords.bit,lifted,logical,Source284FiniteTapeStep.represented,
      Source284FiniteTapeStep.value,Source284FiniteTapeStep.digit,clearBoundary] <;>
    (try split_ifs) <;> omega

/-- Applying the cleared boundary to a serializer output always supplies the
`false :: false :: ...` source end needed by the reflected untagger. -/
theorem clear_canonical (L : List Bool) (b : Bool) (xs : List Bool) :
    clearBoundary (Shared.Codes.FiniteProgramTaggedLoop.canonical L b xs).2 =
      (false::L.tail,false,false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false]) := by
  cases L <;> simp [clearBoundary,Shared.Codes.FiniteProgramTaggedLoop.canonical,
    Shared.ComplexityBridge.PairMarkedScanner.tapeAt]

end Shared.Beeping.NPcoNP.Source284ClearTape

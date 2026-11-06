import Shared.Beeping.NPcoNP.NativeHalfZeroPrefix
import Shared.Beeping.NPcoNP.NativeHalfZeroPrefixFixture

/-! The zero-prefixed suffix's return row, after the independently proved
prepared shift. This is a local table fact, not a whole-program refinement. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfZeroPrefixFixture
open Shared.Beeping.NPcoNP.UnarySuffixShift

theorem selected_zero_prefix_return (base : Int → Bool) (gap : Int) (values : List Nat) :
    machine.step (cfg 31 gap (after base gap (false :: UnaryBank.encode values))) =
      (cfg 18 (gap+1) (after base gap (false :: UnaryBank.encode values)), false) := by
  apply step31_zero
  exact (gap_cells base gap (false :: UnaryBank.encode values)).2.2

theorem selected_zero_prefix_shift_return (base : Int → Bool) (gap : Int) (values : List Nat) :
    let full := false :: UnaryBank.encode values
    silentSegment machine
      (cfg 32 (gap+2) (before base gap full))
      (cfg 18 (gap+1) (after base gap full)) (2*full.length+3) := by
  dsimp only
  have h := selected_zero_prefix_shift base gap values
  have h' := oneSeg machine _ _ (selected_zero_prefix_return base gap values)
  have hh := segAdd machine _ _ _ (2*(false :: UnaryBank.encode values).length+2) 1 h h'
  convert hh using 1 <;> omega
end Shared.Beeping.NPcoNP.NativeHalfSweep

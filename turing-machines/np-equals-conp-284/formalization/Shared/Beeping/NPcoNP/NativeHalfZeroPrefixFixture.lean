import Shared.Beeping.NPcoNP.NativeHalfScan
import Shared.Beeping.NPcoNP.NativeHalfShiftStep
import Shared.Beeping.NPcoNP.UnarySuffixShift
import Shared.Beeping.NPcoNP.UnaryBank

/-! A zero-prefixed scan suffix is outside the ordinary nonempty unary-bank
contract.  The final two consumed units can expose such a delimiter.  These
are prepared local configurations; no global reachability or full HALF
correctness is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroPrefixFixture

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- No nonempty encoded unary bank begins with a zero delimiter. -/
theorem false_prefix_not_encoded (tail : List Bool) (x : Nat) (xs : List Nat) :
    false :: tail ≠ UnaryBank.encode (x :: xs) := by
  simp [UnaryBank.encode, UnaryBank.block, List.replicate_succ]

theorem row31_zero : machine.table.row 31 false = ⟨false, .right, 18, false⟩ := by decide

theorem step31_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 31 h t) = (cfg 18 (h+1) t, false) := by
  have hw : (⟨31, h, t⟩ : Config 284).write false = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row31_zero, Move.apply, hw]

/-- The special all-zero suffix exposes the earlier gap: it reaches state 31
at `gap`, then takes the zero row to state 18.  The whole five-transition
segment is silent and begins from an explicitly supplied tape. -/
theorem zero_suffix_shortcut (base : Int → Bool) (gap : Int) :
    let t := before base gap [false]
    let t' := (cfg 34 (gap+2) t : Config 284).write true
    silentSegment machine (cfg 32 (gap+2) t) (cfg 18 (gap+1) t') 5 := by
  dsimp only
  let t := before base gap [false]
  let t' := (cfg 34 (gap+2) t : Config 284).write true
  have hz0 : t (gap+2) = false := by
    simpa [t, bitAt] using before_suffix_bit base gap [false] 0
  have hz1 : t (gap+3) = false := by
    simpa [t, bitAt, Int.add_assoc] using before_suffix_bit base gap [false] 1
  have scan : silentSegment machine (cfg 32 (gap+2) t) (cfg 34 (gap+2) t) 2 := by
    have h := selected_scan [] Prefix.nil (gap+2) t (by
      simp only [List.nil_append, Holds]
      exact ⟨hz0, by simpa [Int.add_assoc] using hz1, trivial⟩)
    simpa using h
  have hgap1 : t' (gap+1) = false := by
    have hn : gap+1 ≠ gap+2 := by omega
    simpa [t', cfg, Config.write, hn, t] using (gap_cells base gap [false]).2.1
  have hgap : t' gap = false := by
    have hn : gap ≠ gap+2 := by omega
    simpa [t', cfg, Config.write, hn, t] using (gap_cells base gap [false]).1
  have s1 : silentSegment machine (cfg 34 (gap+2) t) (cfg 35 (gap+1) t') 1 := by
    apply oneSeg
    have hp : gap+2-1 = gap+1 := by omega
    simpa [t', cfg, hp] using shift34_zero (gap+2) t hz0
  have s2 : silentSegment machine (cfg 35 (gap+1) t') (cfg 31 gap t') 1 := by
    apply oneSeg
    have hp : gap+1-1 = gap := by omega
    simpa [cfg, hp] using shift35_zero (gap+1) t' hgap1
  have s3 : silentSegment machine (cfg 31 gap t') (cfg 18 (gap+1) t') 1 :=
    oneSeg machine _ _ (step31_zero gap t' hgap)
  have h := segAdd machine _ _ _ 2 1 scan s1
  have h := segAdd machine _ _ _ 3 1 (by simpa using h) s2
  have h := segAdd machine _ _ _ 4 1 (by simpa using h) s3
  exact h

end Shared.Beeping.NPcoNP.NativeHalfZeroPrefixFixture

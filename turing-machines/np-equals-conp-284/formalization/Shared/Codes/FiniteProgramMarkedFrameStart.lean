import Shared.Codes.FiniteProgramFrameStart
import Shared.Codes.FiniteProgramPairStartup

/-! Decode a framed buffer with a distinct marked first word. The underlying
finite table is the existing width-indexed frame decoder. -/
namespace Shared.Codes.FiniteProgramMarkedFrameStart
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems totalCost padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (frames selected selected_length)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

/-- The first metadata bit is dropped with an arbitrary marked word; the
remaining metadata are dropped by the same table and ordinary word selector.
All returned words remain tagged. -/
theorem run_marked (marked zero one : List Bool) (width : Nat)
    (hm : marked.length = width) (hzero : zero.length = width) (hone : one.length = width)
    (first head : Bool) (bits L R : List Bool) :
    let words := marked ++ bits.flatMap (selected zero one)
    run (Shared.Codes.FiniteProgramFrameStart.program width)
      (0,tapeAt L (head::false::tagged ((first::marked) ++ frames zero one bits) ++ false::R))
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) =
      some (.inr (47+empty width, tapeAt (cursor head L words).2
        ((cursor head L words).1::false::false::padding bits.length (false::false::false::R)))) := by
  have hdrop0 := Shared.Codes.FiniteProgramDropTag.drop_first head first (marked ++ frames zero one bits) L R
  have hdrop : run Shared.Codes.FiniteProgramDropTag.program
      (0,tapeAt L (head::false::tagged ((first::marked) ++ frames zero one bits) ++ false::R))
      (30*(width+bits.length*(width+1))+20) =
      some (.inr (47,tapeAt L (head::false::tagged (marked ++ frames zero one bits) ++
        false::false::false::false::R))) := by
    simpa [hm,Shared.Codes.FiniteProgramDropTag.frames_length zero one bits width hzero hone] using hdrop0
  have hfirst := Shared.Codes.FiniteProgramSplice.first_run Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width) Shared.Codes.FiniteProgramDropTag.program_valid
    _ _ _ false (by simp [Shared.Codes.FiniteProgramDropTag.program_length])
    (by simpa [Shared.Codes.FiniteProgramDropTag.program_length] using
      Shared.Codes.FiniteProgramFrameStart.drop_stop) hdrop
  have hw : ∀ item ∈ selectedItems zero one bits, item.2.length = width := by
    intro item hi
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp hi
    exact selected_length zero one width hzero hone bit
  have hloop := Shared.Codes.FiniteProgramFrameLoop.run_frames width (selectedItems zero one bits) hw
    marked L (false::false::false::R) head hm
  rw [Shared.Codes.FiniteProgramFrameLoop.framed_selectedItems,
    Shared.Codes.FiniteProgramFrameLoop.words_selectedItems] at hloop
  have hshift := Shared.Codes.FiniteProgramSplice.second_run Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width) (Shared.Codes.FiniteProgramFrameLoop.program_valid width)
    (0,tapeAt L (head::false::tagged (marked ++ frames zero one bits) ++
      false::false::false::false::R))
    (by simp [Shared.Codes.FiniteProgramFrameLoop.length]) (totalCost width (selectedItems zero one bits))
  rw [hloop] at hshift
  dsimp only
  change run (Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width)) _ _ = _
  rw [run_continue _ _ _ _ _ hfirst]
  simpa only [Shared.Codes.FiniteProgramDropTag.program_length,shiftConfig,shiftStatus,
    Nat.reduceSub,Nat.add_zero,List.cons_append,selectedItems,List.length_map] using hshift

/-- The same decoder-cost bound applies to a distinct marked first word. -/
theorem run_marked_cost_bound (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bits : List Bool) :
    30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits) ≤
      30*(width+bits.length*(width+1))+20 + (bits.length+1)*
        (7*width+30*((bits.length+1)*(width+1))+26) :=
  Shared.Codes.FiniteProgramFrameStart.nonempty_cost_bound zero one width hzero hone bits

end Shared.Codes.FiniteProgramMarkedFrameStart

import Shared.Codes.FiniteProgramFrameLoop

/-! Connect the first metadata removal to the repeating fixed-width frame
loop. The source buffer must already be present with its boundary marker. -/
namespace Shared.Codes.FiniteProgramFrameStart
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus step_shift)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems totalCost padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (frames selected selected_length)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (width : Nat) : Program :=
  Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width)

theorem program_valid (width : Nat) : valid (program width) = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _
    Shared.Codes.FiniteProgramDropTag.program_valid (Shared.Codes.FiniteProgramFrameLoop.program_valid width)

theorem program_length (width : Nat) : (program width).length = 8*width+102 := by
  simp [program,Shared.Codes.FiniteProgramSplice.program,link,
    Shared.Codes.FiniteProgramSplice.stem_length,Shared.Codes.FiniteProgramDropTag.program_length,
    Shared.Codes.FiniteProgramFrameLoop.length]
  omega

/-- The last row of the first removal stage is a terminal fixture; it can
therefore be spliced without changing any earlier execution. -/
theorem drop_stop (t : Tape) :
    step Shared.Codes.FiniteProgramDropTag.program (47,t) = some (.inl false) := by
  have h := step_shift Shared.Codes.FiniteProgramFrameProbe.pre
    Shared.Codes.FiniteProgramDropTag.program [Shared.Codes.FiniteProgramFrameProbe.dummy] (47,t)
    (by simp [Shared.Codes.FiniteProgramDropTag.program_length])
  have hbase := Shared.Codes.FiniteProgramFrameLoop.zero_stop t
  change step (Shared.Codes.FiniteProgramFrameProbe.base) (52,t) = some (.inl false) at hbase
  change step (Shared.Codes.FiniteProgramFrameProbe.base) (52,t) = _ at h
  rw [hbase] at h
  cases hs : step Shared.Codes.FiniteProgramDropTag.program (47,t) with
  | none => simp [hs,shiftStatus] at h
  | some s =>
    cases s with
    | inl b =>
      cases b with
      | false => rfl
      | true =>
        simp only [hs,shiftStatus,Option.some.injEq,Sum.inl.injEq] at h
        contradiction
    | inr c => simp [hs,shiftStatus] at h

/-- Starting with a nonempty framed buffer, remove the first metadata block,
then run the same width-indexed table across all remaining frames and exit.
The retained word bits are still tagged. -/
theorem run_nonempty (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (first b : Bool) (bits L R : List Bool) :
    let allWords := selected zero one first ++ bits.flatMap (selected zero one)
    run (program width) (0,tapeAt L (b::false::tagged (frames zero one (first::bits)) ++ false::R))
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) =
      some (.inr (47+empty width, tapeAt (cursor b L allWords).2
        ((cursor b L allWords).1::false::false::padding bits.length (false::false::false::R)))) := by
  have hdrop := Shared.Codes.FiniteProgramDropTag.drop_first_frame zero one width hzero hone b first bits L R
  have hfirst := Shared.Codes.FiniteProgramSplice.first_run Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width) Shared.Codes.FiniteProgramDropTag.program_valid
    _ _ _ false (by simp [Shared.Codes.FiniteProgramDropTag.program_length])
    (by simpa [Shared.Codes.FiniteProgramDropTag.program_length] using drop_stop) hdrop
  have hloop := Shared.Codes.FiniteProgramFrameLoop.run_selected_frames zero one width hzero hone first b bits L
    (false::false::false::R)
  have hshift := Shared.Codes.FiniteProgramSplice.second_run Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width)
    (Shared.Codes.FiniteProgramFrameLoop.program_valid width)
    (0,tapeAt L (b::false::tagged (selected zero one first ++ frames zero one bits) ++
      false::false::false::false::R))
    (by simp [Shared.Codes.FiniteProgramFrameLoop.length]) (totalCost width (selectedItems zero one bits))
  rw [hloop] at hshift
  dsimp only
  change run (Shared.Codes.FiniteProgramSplice.program Shared.Codes.FiniteProgramDropTag.program
    (Shared.Codes.FiniteProgramFrameLoop.program width)) _ _ = _
  rw [run_continue _ _ _ _ _ hfirst]
  simpa only [Shared.Codes.FiniteProgramDropTag.program_length,shiftConfig,shiftStatus,
    Nat.reduceSub,Nat.add_zero,List.cons_append] using hshift

/-- The initial metadata removal plus all later passes has an explicit
quadratic bound in the number of remaining frames. -/
theorem nonempty_cost_bound (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bits : List Bool) :
    30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits) ≤
      30*(width+bits.length*(width+1))+20 + (bits.length+1)*
        (7*width+30*((bits.length+1)*(width+1))+26) := by
  apply Nat.add_le_add_left
  have hw : ∀ item ∈ selectedItems zero one bits, item.2.length = width := by
    intro item hi
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp hi
    exact selected_length zero one width hzero hone bit
  simpa [selectedItems] using Shared.Codes.FiniteProgramFrameLoop.totalCost_bound width
    (selectedItems zero one bits) hw

/-- The existing first-component scanner's nonempty output has precisely a
leading false metadata datum followed by these remaining framed bits. -/
theorem scan_buffer (zero one todo : List Bool) (bit : Bool) :
    Shared.Codes.FiniteProgramFirstBlocksController.loopOutput zero one (bit::todo) [] =
      frames zero one (false::true::bit::true::true::true::
        Shared.ComplexityBridge.FirstBlocksContent.rawBlocks todo) := by
  rw [Shared.ComplexityBridge.FirstBlocksContent.loop_buffer]
  simp [Shared.ComplexityBridge.FirstBlocksContent.rawBlocks]

/-- The same finite table applies directly to the nonempty first-block scan
buffer. This is a buffer-content handoff; it does not yet splice the scanner
and decoder tables or establish their initial tape layout. -/
theorem run_scan_buffer (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (bit b : Bool) (todo L R : List Bool) :
    let bits := true::bit::true::true::true::Shared.ComplexityBridge.FirstBlocksContent.rawBlocks todo
    let allWords := selected zero one false ++ bits.flatMap (selected zero one)
    run (program width) (0,tapeAt L (b::false::tagged
      (Shared.Codes.FiniteProgramFirstBlocksController.loopOutput zero one (bit::todo) []) ++ false::R))
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) =
      some (.inr (47+empty width, tapeAt (cursor b L allWords).2
        ((cursor b L allWords).1::false::false::padding bits.length (false::false::false::R)))) := by
  rw [scan_buffer]
  exact run_nonempty zero one width hzero hone false b _ L R

end Shared.Codes.FiniteProgramFrameStart

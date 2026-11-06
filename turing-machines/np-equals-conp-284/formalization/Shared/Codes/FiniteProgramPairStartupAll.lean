import Shared.Codes.FiniteProgramPairStartup
import Shared.Codes.FiniteProgramMarkedContinuationAll
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! The marked-pair scanner's terminal tape matches the aligned entry of the
marked witness serializer. This module only covers nonempty witnesses. -/
namespace Shared.Codes.FiniteProgramPairStartupAll
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTaggedLoop (output cost totalCost)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (markedPair consumed tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft markerLeft)
open Shared.ComplexityBridge.PairReverseFirst (expanded)

abbrev scanner_entry_tape := Shared.Codes.FiniteProgramPairStartup.scanner_entry_tape

abbrev payload := Shared.Codes.FiniteProgramMarkedContinuationAll.program

def scanPrefix : Program := Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0) []
def program (mz mo z o : List Bool) : Program := link scanPrefix (payload mz mo z o) []

theorem scanPrefix_length : scanPrefix.length = 5 := rfl

theorem program_length (mz mo z o : List Bool) :
    (program mz mo z o).length = 550+3*mz.length+3*mo.length+36*z.length+36*o.length := by
  simp [program,link,scanPrefix_length,Shared.Codes.FiniteProgramMarkedContinuationAll.program_length]
  omega

theorem program_eq_scanner (mz mo z o : List Bool) :
    program mz mo z o = Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
      ((payload mz mo z o).map (shiftPair 5)) := by
  simp [program,link,scanPrefix,Shared.ComplexityBridge.PairMarkedScanner.program]

/-- Relinking preserves the checked scanner while extending the payload. -/
theorem program_valid (mz mo z o : List Bool) : valid (program mz mo z o) = true := by
  apply Shared.Codes.FiniteProgramRelink.valid_relink scanPrefix
    (Shared.Codes.FiniteProgramMarkedContinuation.program mz mo z o) (payload mz mo z o)
  · exact Shared.Codes.FiniteProgramPairStartup.program_valid mz mo z o
  · exact Shared.Codes.FiniteProgramMarkedContinuationAll.program_valid mz mo z o
  · rw [Shared.Codes.FiniteProgramMarkedContinuation.program_length,
      Shared.Codes.FiniteProgramMarkedContinuationAll.program_length]
    omega

/-- The initial scan and one left move have a linear exact transition cost. -/
theorem setup_cost (x earlier : List Bool) (b : Bool) :
    (BitstringEncoding.bitEncode (x,earlier++[b])).length+1 =
      6*x.length+3*(earlier.length+1)+2 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  simp
  omega

private theorem program_link (mz mo z o : List Bool) : link scanPrefix (payload mz mo z o) [] = program mz mo z o := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program

/-- From the canonical pair input, the literal table marks the separator,
returns to the last witness bit, processes the marked witness and the
first component, including the empty list. All initialization transitions are charged. -/
theorem run_pair (mz mo z o x earlier : List Bool) (b : Bool) :
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    ∃ d, run (program mz mo z o) (initial input)
        (input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost z o x.reverse
            (output z o false buf)))))) = some (.inr d) ∧
      d.1 = 5+(Shared.Codes.FiniteProgramMarkedContinuationAll.pre mz mo z o).length +
        (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirstAll.offset z o +
        (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirstAll.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirstAll.firstOutput z o x.reverse (output z o false buf)) []) := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,earlier++[b])
  let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
  let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
  let pc := mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
      (cost z o false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost z o x.reverse (output z o false buf))))
  let t := moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) [])
  have hscan := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ((payload mz mo z o).map (shiftPair 5)) x (earlier++[b])
  change run (Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
    ((payload mz mo z o).map (shiftPair 5))) (initial input) (input.length+1) = some (.inr (5,t)) at hscan
  rw [← program_eq_scanner] at hscan
  have ht := scanner_entry_tape x earlier b
  change TapeRel t (Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) []
    ((expanded x).reverse ++ false::false::[])) at ht
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramMarkedContinuationAll.run_marked_witness_first
    mz mo z o earlier x [] [] b (0,t) rfl ht
  change run (payload mz mo z o) (0,t) pc = _ at hlast
  have hin : ((0,t) : Config).1 < (payload mz mo z o).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramMarkedContinuationAll.program_valid mz mo z o)
  have hs := run_shift scanPrefix (payload mz mo z o) []
    (Shared.Codes.FiniteProgramMarkedContinuationAll.program_valid mz mo z o) (0,t) hin pc
  rw [hlast,program_link] at hs
  refine ⟨shiftConfig 5 last,?_,?_,hlastt⟩
  · change run (program mz mo z o) (initial input) ((input.length+1)+pc) = _
    rw [run_continue _ _ _ _ _ hscan]
    simpa only [scanPrefix_length,shiftConfig,Nat.add_zero,shiftStatus] using hs
  · simp only [shiftConfig,hlastq]
    omega

/-- The combined table's final framed buffer decodes, at the list level, to
the pinned TM2 input translation for this pair. -/
theorem run_tm2_pair (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let finalBuf := Shared.Codes.FiniteProgramSeparatorFirstAll.firstOutput z o x.reverse (output z o false buf)
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++ (expanded x).reverse
    ∃ d, run (program mz mo z o) (initial input)
        (input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost z o x.reverse
            (output z o false buf)))))) = some (.inr d) ∧
      d.1 = 5+(Shared.Codes.FiniteProgramMarkedContinuationAll.pre mz mo z o).length +
        (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirstAll.offset z o +
        (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirstAll.firstTape [] finalBuf []) ∧
      Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1) finalBuf =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm) := by
  dsimp only
  obtain ⟨d,hr,hd,htape⟩ := run_pair
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true) x earlier b
  refine ⟨d,hr,hd,htape,?_⟩
  exact Shared.Codes.FiniteProgramMarkedWitness.marked_buffer_unframes_tm2 tm enc inp x earlier b

/-- The raw-pair setup adds a linear cost to the polynomial marked serializer
bound. The bound counts finite-table transitions rather than unit-cost integer
operations. -/
theorem pair_cost_bound (mz mo z o x earlier : List Bool) (b : Bool) :
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
    let gw := 3*(1+w)
    let gx := 6*(1+w)
    let start := 1+mz.length+2*(1+w)
    let bulk := start+earlier.length*gw
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
      (cost z o false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost z o x.reverse (output z o false buf))))) ≤
      (6*x.length+3*(earlier.length+1)+2) +
      ((16*mz.length+31 + (2*(16*(1+mz.length+2*(1+w))+16*w+31)+2)) + 2 +
        (earlier.length*(3*(16*(start+earlier.length*gw+gw)+16*w+31)+4)+2+
          (16*bulk+16*w+31 + (4+x.length*(6*(16*(bulk+1+w+x.length*gx+gx)+16*w+31)+4))))) := by
  dsimp only
  have h := Shared.Codes.FiniteProgramMarkedContinuationAll.total_cost_bound mz mo z o earlier x [] b
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at h
  rw [setup_cost]
  exact Nat.add_le_add_left h _

namespace Fixtures
example : valid (program [true] [false] [false] [true]) = true :=
  program_valid [true] [false] [false] [true]
example : (program [true] [false] [false] [true]).length = 628 := by
  simpa using program_length [true] [false] [false] [true]
example : (BitstringEncoding.bitEncode (([false] : List Bool),[true])).length+1 = 11 := by decide
end Fixtures

end Shared.Codes.FiniteProgramPairStartupAll

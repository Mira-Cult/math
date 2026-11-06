import Shared.Codes.FiniteProgramMarkedContinuation
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! The marked-pair scanner's terminal tape matches the aligned entry of the
marked witness serializer. This module only covers nonempty witnesses. -/
namespace Shared.Codes.FiniteProgramPairStartup
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTaggedLoop (output cost totalCost)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (markedPair consumed tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft markerLeft)
open Shared.ComplexityBridge.PairReverseFirst (expanded)

/-- Explicitly adding blank cells at either end of the finite tape lists does
not change the represented bi-infinite tape. -/
theorem tape_padding (left right : List Bool) (head : Bool) :
    TapeRel (left,head,right) (left++[false,false],head,right++[false,false,false]) := by
  unfold TapeRel
  change (⟨head,Turing.ListBlank.mk left,Turing.ListBlank.mk right⟩ : Turing.Tape Bool) =
    ⟨head,Turing.ListBlank.mk (left++[false,false]),Turing.ListBlank.mk (right++[false,false,false])⟩
  have hl : Turing.ListBlank.mk left = Turing.ListBlank.mk (left++[false,false]) := by
    apply Quotient.sound
    exact Or.inl ⟨2,by simp⟩
  have hr : Turing.ListBlank.mk right = Turing.ListBlank.mk (right++[false,false,false]) := by
    apply Quotient.sound
    exact Or.inl ⟨3,by simp⟩
  rw [hl,hr]

/-- After the charged left move from the scanner's end, a nonempty witness
has exactly the marked serializer's entry tape, modulo blank padding. -/
theorem scanner_entry_tape (x earlier : List Bool) (b : Bool) :
    TapeRel
      (moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) []))
      (Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) []
        ((expanded x).reverse ++ false::false::[])) := by
  have hr := Shared.ComplexityBridge.PairReverseWitness.markedPair_reverse x (earlier++[b])
  rw [Shared.ComplexityBridge.PairReverseFirst.markerLeft_eq] at hr
  have hw : (BitstringEncoding.bitEncode (earlier++[b])).reverse =
      false::b::true::(BitstringEncoding.bitEncode earlier).reverse := by
    rw [Shared.ComplexityBridge.PairReverseWitness.encode_append,
      Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simp [hnil,List.reverse_append]
  rw [hw] at hr
  let left := b::true::((BitstringEncoding.bitEncode earlier).reverse ++ true::(expanded x).reverse)
  have hsrc : moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) []) =
      (left,false,[false]) := by
    simp [moveTape,tapeAt,consumed,hr,left]
  have htgt : Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) []
      ((expanded x).reverse ++ false::false::[]) = (left++[false,false],false,[false,false,false,false]) := by
    simp [Shared.Codes.FiniteProgramWitnessPhases.witnessTape,
      Shared.Codes.FiniteProgramWitnessPhases.witnessSource,
      Shared.Codes.FiniteProgramBitShuttle.tagged,tapeLeft,hw,left,List.append_assoc]
  rw [hsrc,htgt]
  simpa using tape_padding left [false] false

abbrev payload := Shared.Codes.FiniteProgramMarkedContinuation.program

def scanPrefix : Program := Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0) []
def program (mz mo z o : List Bool) : Program := link scanPrefix (payload mz mo z o) []

theorem scanPrefix_length : scanPrefix.length = 5 := rfl

theorem program_length (mz mo z o : List Bool) :
    (program mz mo z o).length = 544+3*mz.length+3*mo.length+36*z.length+36*o.length := by
  simp [program,link,scanPrefix_length,Shared.Codes.FiniteProgramMarkedContinuation.program_length]
  omega

theorem program_eq_scanner (mz mo z o : List Bool) :
    program mz mo z o = Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
      ((payload mz mo z o).map (shiftPair 5)) := by
  simp [program,link,scanPrefix,Shared.ComplexityBridge.PairMarkedScanner.program]

/-- The scanner's final dispatch is charged, and every numeric destination in
the scanner scanPrefix and the relocated payload is in range. -/
theorem program_valid (mz mo z o : List Bool) : valid (program mz mo z o) = true := by
  let d := payload mz mo z o
  let m := 5+d.length
  have hpos : 0 < d.length := Shared.Codes.FiniteProgramLink.valid_nonempty d
    (Shared.Codes.FiniteProgramMarkedContinuation.program_valid mz mo z o)
  have hm : (program mz mo z o).length = m := by simp [program,link,scanPrefix_length,m,d]
  have hp : ∀ r ∈ scanPrefix, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hall : scanPrefix.all (fun r => validRow m r.1 && validRow m r.2) = true := by
      have h5 : 5 < m := by dsimp [m]; omega
      simp [scanPrefix,Shared.ComplexityBridge.PairMarkedScanner.program,validRow,h5]
      omega
    rw [List.all_eq_true] at hall
    simpa only [Bool.and_eq_true] using hall r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramMarkedContinuation.program_valid mz mo z o
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hall : (program mz mo z o).all
      (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ scanPrefix ∨ r ∈ d.map (shiftPair 5) := by
      simpa [program,link,scanPrefix_length,d,List.mem_append] using hr
    rw [hm]
    rcases hr' with hpre | hmap
    · simpa only [Bool.and_eq_true] using hp r hpre
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 5 d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 5 d.length h₂⟩
  have hn : (program mz mo z o).isEmpty = false := by
    cases h : program mz mo z o with
    | nil => simp [h] at hm; dsimp [m] at hm; omega
    | cons r rs => rfl
  change (!(program mz mo z o).isEmpty && (program mz mo z o).all
    (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2)) = true
  rw [hn,hall]
  rfl

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
nonempty first component. All initialization transitions are charged. -/
theorem run_pair (mz mo z o x earlier : List Bool) (b : Bool) (hx : x ≠ []) :
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    ∃ d, run (program mz mo z o) (initial input)
        (input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
            (output z o false buf))))) = some (.inr d) ∧
      d.1 = 5+(Shared.Codes.FiniteProgramMarkedContinuation.pre mz mo z o).length +
        (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false buf)) []) := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,earlier++[b])
  let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
  let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
  let pc := mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
      (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse (output z o false buf)))
  let t := moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) [])
  have hscan := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ((payload mz mo z o).map (shiftPair 5)) x (earlier++[b])
  change run (Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
    ((payload mz mo z o).map (shiftPair 5))) (initial input) (input.length+1) = some (.inr (5,t)) at hscan
  rw [← program_eq_scanner] at hscan
  have ht := scanner_entry_tape x earlier b
  change TapeRel t (Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) []
    ((expanded x).reverse ++ false::false::[])) at ht
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramMarkedContinuation.run_marked_witness_first
    mz mo z o earlier x [] [] b hx (0,t) rfl ht
  change run (payload mz mo z o) (0,t) pc = _ at hlast
  have hin : ((0,t) : Config).1 < (payload mz mo z o).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramMarkedContinuation.program_valid mz mo z o)
  have hs := run_shift scanPrefix (payload mz mo z o) []
    (Shared.Codes.FiniteProgramMarkedContinuation.program_valid mz mo z o) (0,t) hin pc
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
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) (hx : x ≠ []) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let finalBuf := Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false buf)
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++ (expanded x).reverse
    ∃ d, run (program mz mo z o) (initial input)
        (input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
            (output z o false buf))))) = some (.inr d) ∧
      d.1 = 5+(Shared.Codes.FiniteProgramMarkedContinuation.pre mz mo z o).length +
        (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape [] finalBuf []) ∧
      Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1) finalBuf =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm) := by
  dsimp only
  obtain ⟨d,hr,hd,htape⟩ := run_pair
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true) x earlier b hx
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
      (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse (output z o false buf)))) ≤
      (6*x.length+3*(earlier.length+1)+2) +
      ((16*mz.length+31 + (2*(16*(1+mz.length+2*(1+w))+16*w+31)+2)) + 2 +
        (earlier.length*(3*(16*(start+earlier.length*gw+gw)+16*w+31)+4)+2+
          (16*bulk+16*w+31 + x.length*(6*(16*(bulk+1+w+x.length*gx+gx)+16*w+31)+4)))) := by
  dsimp only
  have h := Shared.Codes.FiniteProgramMarkedContinuation.total_cost_bound mz mo z o earlier x [] b
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at h
  rw [setup_cost]
  exact Nat.add_le_add_left h _

namespace Fixtures
example : valid (program [true] [false] [false] [true]) = true :=
  program_valid [true] [false] [false] [true]
example : (program [true] [false] [false] [true]).length = 622 := by
  simpa using program_length [true] [false] [false] [true]
example : (BitstringEncoding.bitEncode (([false] : List Bool),[true])).length+1 = 11 := by decide
end Fixtures

end Shared.Codes.FiniteProgramPairStartup

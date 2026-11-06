import Shared.Codes.FiniteProgramMarkedSeparatorFirst
import Shared.Codes.FiniteProgramPairStartup
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! A separate marked-separator path for the empty-witness pair. -/
namespace Shared.Codes.FiniteProgramEmptyWitness
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.Codes.FiniteProgramExtendAdvance (bridge)
open Shared.ComplexityBridge.PairMarkedScanner (markedPair consumed tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev payload := Shared.Codes.FiniteProgramMarkedSeparatorFirst.program

def pre : Program :=
  Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
    [Shared.Codes.FiniteProgramWitnessFirst.restoreRow 6,bridge 7]

def program (mz mo z o : List Bool) : Program := link pre (payload mz mo z o) []

theorem prefix_length : pre.length = 7 := rfl

theorem program_length (mz mo z o : List Bool) :
    (program mz mo z o).length = 298+3*mz.length+3*mo.length+18*z.length+18*o.length := by
  simp [program,link,prefix_length,Shared.Codes.FiniteProgramMarkedSeparatorFirst.program_length]
  omega

theorem program_eq_scanner (mz mo z o : List Bool) :
    program mz mo z o = Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
      ([Shared.Codes.FiniteProgramWitnessFirst.restoreRow 6,bridge 7] ++
        (payload mz mo z o).map (shiftPair 7)) := by
  simp [program,link,pre,Shared.ComplexityBridge.PairMarkedScanner.program]

theorem program_valid (mz mo z o : List Bool) : valid (program mz mo z o) = true := by
  let d := payload mz mo z o
  let m := 7+d.length
  have hpos : 0 < d.length := Shared.Codes.FiniteProgramLink.valid_nonempty d
    (Shared.Codes.FiniteProgramMarkedSeparatorFirst.program_valid mz mo z o)
  have hm : (program mz mo z o).length = m := by simp [program,link,prefix_length,m,d]
  have hp : ∀ r ∈ pre, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hall : pre.all (fun r => validRow m r.1 && validRow m r.2) = true := by
      have h7 : 7 < m := by dsimp [m]; omega
      simp [pre,Shared.ComplexityBridge.PairMarkedScanner.program,Shared.Codes.FiniteProgramWitnessFirst.restoreRow,bridge,validRow,h7]
      omega
    rw [List.all_eq_true] at hall
    simpa only [Bool.and_eq_true] using hall r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramMarkedSeparatorFirst.program_valid mz mo z o
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hall : (program mz mo z o).all
      (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre ∨ r ∈ d.map (shiftPair 7) := by
      simpa [program,link,prefix_length,d,List.mem_append] using hr
    rw [hm]
    rcases hr' with hpre | hmap
    · simpa only [Bool.and_eq_true] using hp r hpre
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 7 d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 7 d.length h₂⟩
  have hn : (program mz mo z o).isEmpty = false := by
    cases h : program mz mo z o with
    | nil => simp [h] at hm; dsimp [m] at hm; omega
    | cons r rs => rfl
  change (!(program mz mo z o).isEmpty && (program mz mo z o).all
    (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2)) = true
  rw [hn,hall]
  rfl

/-- After the initial scan, the empty witness puts the marked separator under
    the head, with an empty buffer and the first component to its left. -/
theorem scanner_entry_tape (x : List Bool) :
    TapeRel (moveTape true false (tapeAt (consumed [] (markedPair x [])) []))
      (tapeAt ((expanded x).reverse ++ [false,false]) [true,false,false,false,false]) := by
  have hr := Shared.ComplexityBridge.PairReverseWitness.markedPair_reverse x []
  rw [Shared.ComplexityBridge.PairReverseFirst.markerLeft_eq] at hr
  have hz : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
  simp only [hz,List.reverse_nil,List.nil_append] at hr
  have hsrc : moveTape true false (tapeAt (consumed [] (markedPair x [])) []) =
      ((expanded x).reverse,true,[false]) := by
    simp [moveTape,tapeAt,consumed,hr]
  rw [hsrc]
  simpa [tapeAt] using Shared.Codes.FiniteProgramPairStartup.tape_padding ((expanded x).reverse) [false] true

theorem restore (mz mo z o : List Bool) (L : List Bool) :
    run (program mz mo z o) (5,tapeAt L [true,false,false,false,false]) 2 =
      some (.inr (7,tapeAt L [false,false,false,false,false])) := by
  simp [program,link,pre,Shared.ComplexityBridge.PairMarkedScanner.program,
    Shared.Codes.FiniteProgramWitnessFirst.restoreRow,bridge,run,advance,step,tapeAt,moveTape]

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program

/-- Starting from the actual encoded pair, scan and restore the marked
separator, then execute its marked-word phase and all first-component blocks.
The witness is empty; the first component may also be empty. -/
theorem run_empty_witness (mz mo z o x : List Bool) :
    let input := BitstringEncoding.bitEncode (x,([] : List Bool))
    let buf := Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput z o x.reverse (output mz mo false [])
    let pc := cost mz mo false [] + (4+Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstCost z o x.reverse (output mz mo false []))
    ∃ d, run (program mz mo z o) (initial input) (input.length+1+2+pc) = some (.inr d) ∧
      d.1 = 7+Shared.Codes.FiniteProgramMarkedSeparatorFirst.offset mz mo +
        (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstTape [] buf []) := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,([] : List Bool))
  let left := (expanded x).reverse ++ [false,false]
  let raw := moveTape true false (tapeAt (consumed [] (markedPair x [])) [])
  let marked := tapeAt left [true,false,false,false,false]
  let restored := tapeAt left [false,false,false,false,false]
  let pc := cost mz mo false [] + (4+Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstCost z o x.reverse (output mz mo false []))
  have hscan := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ([Shared.Codes.FiniteProgramWitnessFirst.restoreRow 6,bridge 7] ++
      (payload mz mo z o).map (shiftPair 7)) x []
  change run _ (initial input) (input.length+1) = some (.inr (5,raw)) at hscan
  rw [← program_eq_scanner] at hscan
  have ht : TapeRel raw marked := scanner_entry_tape x
  have hr := run_related (program mz mo z o) (5,raw) (5,marked) rfl ht 2
  have hrestore := restore mz mo z o left
  change run (program mz mo z o) (5,marked) 2 = some (.inr (7,restored)) at hrestore
  rw [hrestore] at hr
  obtain ⟨start,hstart,hq,htape⟩ := status_live _ _ _ hr
  have htape' : TapeRel start.2 (canonical ((expanded x).reverse ++ false::false::[]) false []).2 := by
    simpa [restored,left,canonical,Shared.Codes.FiniteProgramBitShuttle.tagged,tapeAt] using htape
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramMarkedSeparatorFirst.run_separator_first
    mz mo z o x [] [] (0,start.2) rfl htape'
  have hin : ((0,start.2) : Config).1 < (payload mz mo z o).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramMarkedSeparatorFirst.program_valid mz mo z o)
  have hs := run_shift pre (payload mz mo z o) []
    (Shared.Codes.FiniteProgramMarkedSeparatorFirst.program_valid mz mo z o) (0,start.2) hin pc
  rw [hlast] at hs
  have hcfg : start = shiftConfig pre.length (0,start.2) := by
    apply Prod.ext
    · simpa [shiftConfig,prefix_length] using hq
    · rfl
  refine ⟨shiftConfig 7 last,?_,?_,hlastt⟩
  · change run (program mz mo z o) (initial input) ((input.length+1)+2+pc) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hscan,run_continue _ _ _ _ _ hstart,hcfg]
    simpa only [program,prefix_length,shiftStatus] using hs
  · simp only [shiftConfig,hlastq]
    omega


/-- The marked separator is the first frame; the remaining frames are the
    reversed first-component cells. -/
theorem buffer_content (mz mo z o x : List Bool) :
    Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput z o x.reverse (output mz mo false []) =
      (false::mz) ++ Shared.ComplexityBridge.FirstBlocksContent.frames z o (expanded x).reverse := by
  unfold Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput
  rw [Shared.ComplexityBridge.FirstBlocksContent.loop_buffer,
    Shared.ComplexityBridge.FirstBlocksContent.rawBlocks_eq_reverse_expanded]
  simp [output]

/-- The canonical empty-witness pair ends in the separator bit. -/
theorem pair_reverse (x : List Bool) :
    (BitstringEncoding.bitEncode (x,([] : List Bool))).reverse = false::(expanded x).reverse := by
  rw [Shared.ComplexityBridge.PairReverseFirst.pair_encoding]
  have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
  simp [hnil,List.reverse_append]

/-- List-level removal of the frames gives the canonical translated TM2
    input. Physical frame removal is a separate obligation. -/
theorem unframe_tm2 (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    Shared.ComplexityBridge.FirstBlocksContent.unframe width ((expanded x).length+1)
      (Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput z o x.reverse (output mz mo false [])) =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm) := by
  dsimp only
  rw [buffer_content]
  rw [show (expanded x).length+1 = ((expanded x).reverse).length+1 by simp]
  rw [Shared.Codes.FiniteProgramMarkedWitness.unframe_marked _ _ _ width
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)]
  have hrev : ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm).reverse =
      inp.symm false :: ((expanded x).reverse).map inp.symm := by
    rw [← List.map_reverse,pair_reverse]
    rfl
  rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
  simp only [List.flatMap_map]
  have hs : Shared.ComplexityBridge.FirstBlocksContent.selected
      (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
      (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true) =
      Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
    funext b; cases b <;> rfl
  rw [hs]
  rfl


/-- The finite run and list-level interpretation agree with the TM2 input
    for an empty witness, including the empty first component. -/
theorem run_tm2_empty_witness (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,([] : List Bool))
    let buf := Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput z o x.reverse (output mz mo false [])
    let pc := cost mz mo false [] + (4+Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstCost z o x.reverse (output mz mo false []))
    ∃ d, run (program mz mo z o) (initial input) (input.length+1+2+pc) = some (.inr d) ∧
      d.1 = 7+Shared.Codes.FiniteProgramMarkedSeparatorFirst.offset mz mo +
        (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstTape [] buf []) ∧
      Shared.ComplexityBridge.FirstBlocksContent.unframe width ((expanded x).length+1) buf =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm) := by
  dsimp only
  obtain ⟨d,hr,hstate,htape⟩ := run_empty_witness
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true) x
  exact ⟨d,hr,hstate,htape,unframe_tm2 tm enc inp x⟩

/-- Polynomial bound in encoded first-component length and table word sizes,
    counting the scanner, marker restoration, guard, and all scan cycles. -/
theorem total_cost_bound (mz mo z o x : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
    let gain := 6*(1+w)
    (BitstringEncoding.bitEncode (x,([] : List Bool))).length+1+2+
      (cost mz mo false [] + (4+Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstCost z o x.reverse (output mz mo false []))) ≤
      (6*x.length+4) + (16*mz.length+31) +
        (4+x.length*(6*(16*(1+mz.length+x.length*gain+gain)+16*w+31)+4)) := by
  have h := Shared.Codes.FiniteProgramMarkedSeparatorFirst.total_cost_bound mz mo z o x []
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at h
  have hi := Shared.ComplexityBridge.bitstring_pair_encoded_length x ([] : List Bool)
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hi
  dsimp only
  omega

namespace Fixtures
example : valid (program [true] [false] [false] [true]) = true :=
  program_valid [true] [false] [false] [true]
example : ∃ n d, run (program [] [] [] [])
    (initial (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool)))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_empty_witness [] [] [] [] []
  exact ⟨_,d,hr⟩
example : ∃ n d, run (program [] [] [] [])
    (initial (BitstringEncoding.bitEncode (([true] : List Bool),([] : List Bool)))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_empty_witness [] [] [] [] [true]
  exact ⟨_,d,hr⟩
end Fixtures

end Shared.Codes.FiniteProgramEmptyWitness

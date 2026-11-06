import Shared.Codes.FiniteProgramPairHeadAll
import Shared.Codes.FiniteProgramEmptyWitnessHead
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Scan an encoded pair and dispatch on the final input bit. For a canonical
pair it is false when the witness is nonempty and true when it is empty: the
latter is the temporarily marked separator. Each branch returns the head to
its original cell before entering state 5 of a separately linked table. -/
namespace Shared.Codes.FiniteProgramPairDispatch
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (bridge)
open Shared.ComplexityBridge.PairMarkedScanner (markedPair consumed tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def pre (n : Program) : Program :=
  Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
    [((false,true,6,0),(true,true,7,0)),bridge 13,bridge (13+n.length)]

def program (n e : Program) : Program :=
  link (pre n) n (e.map (shiftPair (8+n.length)))

theorem pre_length (n : Program) : (pre n).length = 8 := rfl

theorem program_length (n e : Program) : (program n e).length = 8+n.length+e.length := by
  simp [program,link,pre_length,Nat.add_assoc]

theorem eq_scanner (n e : Program) :
    program n e = Shared.ComplexityBridge.PairMarkedScanner.program (false,false,5,0)
      ([((false,true,6,0),(true,true,7,0)),bridge 13,bridge (13+n.length)] ++
        n.map (shiftPair 8) ++ e.map (shiftPair (8+n.length))) := by
  simp [program,link,pre,Shared.ComplexityBridge.PairMarkedScanner.program]

theorem dispatch_false (n e : Program) (L R : List Bool) :
    run (program n e) (5,tapeAt L (false::false::R)) 2 =
      some (.inr (13,tapeAt L (false::false::R))) := by
  simp [program,link,pre,Shared.ComplexityBridge.PairMarkedScanner.program,
    bridge,run,advance,step,tapeAt,moveTape]

theorem dispatch_true (n e : Program) (L R : List Bool) :
    run (program n e) (5,tapeAt L (true::false::R)) 2 =
      some (.inr (13+n.length,tapeAt L (true::false::R))) := by
  simp [program,link,pre,Shared.ComplexityBridge.PairMarkedScanner.program,
    bridge,run,advance,step,tapeAt,moveTape]

/-- The false branch relocates every finite continuation run exactly. -/
theorem run_nonempty_branch (n e : Program) (hn : valid n = true) (t : Tape)
    (h5 : 5 < n.length) (k : Nat) :
    run (program n e) (shiftConfig 8 (5,t)) k = shiftStatus 8 (run n (5,t) k) := by
  simpa only [program,pre_length] using
    run_shift (pre n) n (e.map (shiftPair (8+n.length))) hn (5,t) h5 k

/-- The true branch relocates every finite continuation run exactly. -/
theorem run_empty_branch (n e : Program) (he : valid e = true) (t : Tape)
    (h5 : 5 < e.length) (k : Nat) :
    run (program n e) (shiftConfig (8+n.length) (5,t)) k =
      shiftStatus (8+n.length) (run e (5,t) k) := by
  have hp : program n e = link (pre n ++ n.map (shiftPair 8)) e [] := by
    simp [program,link,pre_length,List.append_assoc]
  rw [hp]
  have h := run_shift (pre n ++ n.map (shiftPair 8)) e [] he (5,t) h5 k
  simpa only [List.length_append,List.length_map,pre_length] using h

/-- Every row has an in-range target, including both relocated tables. -/
theorem program_valid (n e : Program) (hn : valid n = true) (he : valid e = true)
    (hn5 : 5 < n.length) (he5 : 5 < e.length) : valid (program n e) = true := by
  let m := 8+n.length+e.length
  have hm : (program n e).length = m := program_length n e
  have hp : ∀ r ∈ pre n, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hall : (pre n).all (fun r => validRow m r.1 && validRow m r.2) = true := by
      have h13 : 13 < m := by dsimp [m]; omega
      have h13n : 13+n.length < m := by dsimp [m]; omega
      simp [pre,Shared.ComplexityBridge.PairMarkedScanner.program,bridge,validRow,h13,h13n]
      omega
    rw [List.all_eq_true] at hall
    simpa only [Bool.and_eq_true] using hall r hr
  have hnrows : ∀ r ∈ n, validRow n.length r.1 = true ∧ validRow n.length r.2 = true := by
    intro r hr
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hn
    simpa only [Bool.and_eq_true] using hn.2 r hr
  have herows : ∀ r ∈ e, validRow e.length r.1 = true ∧ validRow e.length r.2 = true := by
    intro r hr
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at he
    simpa only [Bool.and_eq_true] using he.2 r hr
  have hall : (program n e).all
      (fun r => validRow (program n e).length r.1 && validRow (program n e).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre n ∨ r ∈ n.map (shiftPair 8) ∨ r ∈ e.map (shiftPair (8+n.length)) := by
      simpa [program,link,pre_length,List.mem_append] using hr
    rw [hm]
    rcases hr' with hpre | hnmap | hemap
    · simpa only [Bool.and_eq_true] using hp r hpre
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hnmap
      obtain ⟨h₁,h₂⟩ := hnrows r' hr'
      have hle : 8+n.length ≤ m := by dsimp [m]; omega
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle
          (Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 8 n.length h₁),
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle
          (Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 8 n.length h₂)⟩
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hemap
      obtain ⟨h₁,h₂⟩ := herows r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 (8+n.length) e.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 (8+n.length) e.length h₂⟩
  have hne : (program n e).isEmpty = false := by
    cases h : program n e with
    | nil => simp [h] at hm; dsimp [m] at hm; omega
    | cons r rs => rfl
  change (!(program n e).isEmpty && (program n e).all
    (fun r => validRow (program n e).length r.1 && validRow (program n e).length r.2)) = true
  rw [hne,hall]
  rfl


/-- A nonempty witness ends with false, even when its last data bit is true. -/
theorem nonempty_entry_tape (x earlier : List Bool) (b : Bool) :
    moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) []) =
      tapeAt (b::true::((BitstringEncoding.bitEncode earlier).reverse ++
        true::(Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse)) [false,false] := by
  have hr := Shared.ComplexityBridge.PairReverseWitness.markedPair_reverse x (earlier++[b])
  rw [Shared.ComplexityBridge.PairReverseFirst.markerLeft_eq] at hr
  have hw : (BitstringEncoding.bitEncode (earlier++[b])).reverse =
      false::b::true::(BitstringEncoding.bitEncode earlier).reverse := by
    rw [Shared.ComplexityBridge.PairReverseWitness.encode_append,
      Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simp [hnil,List.reverse_append]
  rw [hw] at hr
  simp [moveTape,tapeAt,consumed,hr]

/-- The empty witness leaves the temporarily marked separator under the head. -/
theorem empty_entry_tape (x : List Bool) :
    moveTape true false (tapeAt (consumed [] (markedPair x [])) []) =
      tapeAt (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse [true,false] := by
  have hr := Shared.ComplexityBridge.PairReverseWitness.markedPair_reverse x []
  rw [Shared.ComplexityBridge.PairReverseFirst.markerLeft_eq] at hr
  have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
  simp only [hnil,List.reverse_nil,List.nil_append] at hr
  simp [moveTape,tapeAt,consumed,hr]

/-- Initial scan plus dispatch for a nonempty witness; exactly two additional
    transitions are charged after the scanner's left move. -/
theorem scan_nonempty (n e : Program) (x earlier : List Bool) (b : Bool) :
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let t := moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) [])
    run (program n e) (initial input) (input.length+1+2) = some (.inr (13,t)) := by
  dsimp only
  have hs := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ([((false,true,6,0),(true,true,7,0)),bridge 13,bridge (13+n.length)] ++
      n.map (shiftPair 8) ++ e.map (shiftPair (8+n.length))) x (earlier++[b])
  dsimp only at hs
  rw [← eq_scanner] at hs
  rw [run_continue _ _ _ _ _ hs,nonempty_entry_tape]
  exact dispatch_false n e _ []

/-- Initial scan plus dispatch for an empty witness, with the marked
    separator preserved until its selected continuation restores it. -/
theorem scan_empty (n e : Program) (x : List Bool) :
    let input := BitstringEncoding.bitEncode (x,([] : List Bool))
    let t := moveTape true false (tapeAt (consumed [] (markedPair x [])) [])
    run (program n e) (initial input) (input.length+1+2) = some (.inr (13+n.length,t)) := by
  dsimp only
  have hs := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ([((false,true,6,0),(true,true,7,0)),bridge 13,bridge (13+n.length)] ++
      n.map (shiftPair 8) ++ e.map (shiftPair (8+n.length))) x []
  dsimp only at hs
  rw [← eq_scanner] at hs
  rw [run_continue _ _ _ _ _ hs,empty_entry_tape]
  exact dispatch_true n e _ []

/-- Once the nonempty continuation's run from state 5 is established,
    dispatch preserves it exactly, with the scanner and dispatch time added. -/
theorem run_nonempty_after_scan (n e : Program) (x earlier : List Bool) (b : Bool)
    (hn : valid n = true) (h5 : 5 < n.length) (k : Nat) :
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let t := moveTape true false (tapeAt (consumed [] (markedPair x (earlier++[b]))) [])
    run (program n e) (initial input) (input.length+1+2+k) =
      shiftStatus 8 (run n (5,t) k) := by
  dsimp only
  have hs := scan_nonempty n e x earlier b
  dsimp only at hs
  rw [run_continue _ _ _ _ _ hs]
  simpa only [shiftConfig] using run_nonempty_branch n e hn _ h5 k

/-- The empty continuation is likewise preserved after its branch is chosen. -/
theorem run_empty_after_scan (n e : Program) (x : List Bool)
    (he : valid e = true) (h5 : 5 < e.length) (k : Nat) :
    let input := BitstringEncoding.bitEncode (x,([] : List Bool))
    let t := moveTape true false (tapeAt (consumed [] (markedPair x [])) [])
    run (program n e) (initial input) (input.length+1+2+k) =
      shiftStatus (8+n.length) (run e (5,t) k) := by
  dsimp only
  have hs := scan_empty n e x
  dsimp only at hs
  rw [run_continue _ _ _ _ _ hs]
  have h := run_empty_branch n e he
    (moveTape true false (tapeAt (consumed [] (markedPair x [])) [])) h5 k
  simpa only [shiftConfig,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The generic dispatching table instantiated with the two physical TM2
    input initializers. Their post-dispatch correctness must still be linked. -/
def tm2Program (mz mo z o : List Bool) (width : Nat) : Program :=
  program (Shared.Codes.FiniteProgramPairHeadAll.program mz mo z o width)
    (Shared.Codes.FiniteProgramEmptyWitnessHead.program mz mo z o width)

theorem tm2Program_valid (mz mo z o : List Bool) (width : Nat) :
    valid (tm2Program mz mo z o width) = true := by
  apply program_valid _ _ (Shared.Codes.FiniteProgramPairHeadAll.program_valid mz mo z o width)
    (Shared.Codes.FiniteProgramEmptyWitnessHead.program_valid mz mo z o width)
  · rw [Shared.Codes.FiniteProgramPairHeadAll.program_length]; omega
  · rw [Shared.Codes.FiniteProgramEmptyWitnessHead.program_length]; omega

theorem tm2Program_length (mz mo z o : List Bool) (width : Nat) :
    (tm2Program mz mo z o width).length =
      1154+6*mz.length+6*mo.length+54*z.length+54*o.length+16*width := by
  simp [tm2Program,program_length,Shared.Codes.FiniteProgramPairHeadAll.program_length,
    Shared.Codes.FiniteProgramEmptyWitnessHead.program_length]
  omega

namespace Fixtures
example : valid (tm2Program [true] [false] [false] [true] 1) = true :=
  tm2Program_valid [true] [false] [false] [true] 1
example : run (program [] []) (5,tapeAt [] [false,false]) 2 =
    some (.inr (13,tapeAt [] [false,false])) := dispatch_false [] [] [] []
example : run (program [] []) (5,tapeAt [] [true,false]) 2 =
    some (.inr (13,tapeAt [] [true,false])) := dispatch_true [] [] [] []
end Fixtures

end Shared.Codes.FiniteProgramPairDispatch

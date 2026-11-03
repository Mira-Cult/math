import Shared.Codes.FiniteProgramPairDispatch
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Connect both complete initializer runs to the pair dispatcher. -/
namespace Shared.Codes.FiniteProgramPairUnified
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftPair shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramExtendAdvance (bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.PairMarkedScanner (markedPair consumed tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev nonemptyScan := Shared.Codes.FiniteProgramPairStartupAll.program
abbrev nonemptyDecode := Shared.Codes.FiniteProgramPairDecodeAll.program
abbrev nonemptyHead := Shared.Codes.FiniteProgramPairHeadAll.program
abbrev emptyScan := Shared.Codes.FiniteProgramEmptyWitness.program
abbrev emptyDecode := Shared.Codes.FiniteProgramEmptyWitnessDecode.program
abbrev emptyHead := Shared.Codes.FiniteProgramEmptyWitnessHead.program
abbrev program := Shared.Codes.FiniteProgramPairDispatch.tm2Program

def scannedTape (x w : List Bool) : Tape :=
  moveTape true false (tapeAt (consumed [] (markedPair x w)) [])

/-- The scan prefix survives both terminal-row patches in the nonempty table. -/
theorem nonempty_head_scan (mz mo z o x w : List Bool) (width : Nat) :
    let input := BitstringEncoding.bitEncode (x,w)
    run (nonemptyHead mz mo z o width) (initial input) (input.length+1) =
      some (.inr (5,scannedTape x w)) := by
  dsimp only
  have hs := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ((Shared.Codes.FiniteProgramPairStartupAll.payload mz mo z o).map (shiftPair 5)) x w
  dsimp only at hs
  rw [← Shared.Codes.FiniteProgramPairStartupAll.program_eq_scanner] at hs
  change run (nonemptyScan mz mo z o) _ _ = some (.inr (5,scannedTape x w)) at hs
  have hd := Shared.Codes.FiniteProgramFirstEntry.first_entry (nonemptyScan mz mo z o)
    (nonemptyDecode mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w))) (5,scannedTape x w)
    ((BitstringEncoding.bitEncode (x,w)).length+1) (Shared.Codes.FiniteProgramPairDecodeAll.stop mz mo z o) false
    (Shared.Codes.FiniteProgramPairStartupAll.program_valid mz mo z o)
    (by simpa [initial] using (Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramPairStartupAll.program_valid mz mo z o)))
    (Shared.Codes.FiniteProgramPairDecodeAll.scan_stop mz mo z o)
    (Shared.Codes.FiniteProgramPairDecodeAll.scan_other mz mo z o width) hs
  exact Shared.Codes.FiniteProgramFirstEntry.first_entry (nonemptyDecode mz mo z o width)
    (nonemptyHead mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w))) (5,scannedTape x w)
    ((BitstringEncoding.bitEncode (x,w)).length+1) (Shared.Codes.FiniteProgramPairHeadAll.stop mz mo z o width) false
    (Shared.Codes.FiniteProgramPairDecodeAll.program_valid mz mo z o width)
    (by simpa [initial] using (Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramPairDecodeAll.program_valid mz mo z o width)))
    (Shared.Codes.FiniteProgramPairHeadAll.base_stop mz mo z o width)
    (Shared.Codes.FiniteProgramPairHeadAll.base_other mz mo z o width) hd

/-- The scan prefix survives both terminal-row patches in the empty table. -/
theorem empty_head_scan (mz mo z o x w : List Bool) (width : Nat) :
    let input := BitstringEncoding.bitEncode (x,w)
    run (emptyHead mz mo z o width) (initial input) (input.length+1) =
      some (.inr (5,scannedTape x w)) := by
  dsimp only
  have hs := Shared.ComplexityBridge.PairMarkedScanner.scan_and_enter_reverse 5
    ([Shared.Codes.FiniteProgramWitnessFirst.restoreRow 6,bridge 7] ++
      (Shared.Codes.FiniteProgramEmptyWitness.payload mz mo z o).map (shiftPair 7)) x w
  dsimp only at hs
  rw [← Shared.Codes.FiniteProgramEmptyWitness.program_eq_scanner] at hs
  change run (emptyScan mz mo z o) _ _ = some (.inr (5,scannedTape x w)) at hs
  have hd := Shared.Codes.FiniteProgramFirstEntry.first_entry (emptyScan mz mo z o)
    (emptyDecode mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w))) (5,scannedTape x w)
    ((BitstringEncoding.bitEncode (x,w)).length+1) (Shared.Codes.FiniteProgramEmptyWitnessDecode.stop mz mo z o) false
    (Shared.Codes.FiniteProgramEmptyWitness.program_valid mz mo z o)
    (by simpa [initial] using (Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramEmptyWitness.program_valid mz mo z o)))
    (Shared.Codes.FiniteProgramEmptyWitnessDecode.scan_stop mz mo z o)
    (Shared.Codes.FiniteProgramEmptyWitnessDecode.scan_other mz mo z o width) hs
  exact Shared.Codes.FiniteProgramFirstEntry.first_entry (emptyDecode mz mo z o width)
    (emptyHead mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w))) (5,scannedTape x w)
    ((BitstringEncoding.bitEncode (x,w)).length+1) (Shared.Codes.FiniteProgramEmptyWitnessHead.stop mz mo z o width) false
    (Shared.Codes.FiniteProgramEmptyWitnessDecode.program_valid mz mo z o width)
    (by simpa [initial] using (Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramEmptyWitnessDecode.program_valid mz mo z o width)))
    (Shared.Codes.FiniteProgramEmptyWitnessHead.base_stop mz mo z o width)
    (Shared.Codes.FiniteProgramEmptyWitnessHead.base_other mz mo z o width) hd

/-- Any full run of the nonempty initializer transfers to the unified table
with exactly two extra dispatcher transitions. -/
theorem transfer_nonempty (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (k : Nat) (d : Config)
    (h : run (nonemptyHead mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
      ((BitstringEncoding.bitEncode (x,earlier++[b])).length+1+k) = some (.inr d)) :
    run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
      ((BitstringEncoding.bitEncode (x,earlier++[b])).length+1+2+k) =
        some (.inr (shiftConfig 8 d)) := by
  have hs := nonempty_head_scan mz mo z o x (earlier++[b]) width
  dsimp only at hs
  rw [run_continue _ _ _ _ _ hs] at h
  have hn := Shared.Codes.FiniteProgramPairHeadAll.program_valid mz mo z o width
  have h5 : 5 < (nonemptyHead mz mo z o width).length := by
    rw [Shared.Codes.FiniteProgramPairHeadAll.program_length]; omega
  have ht := Shared.Codes.FiniteProgramPairDispatch.run_nonempty_after_scan
    (nonemptyHead mz mo z o width) (emptyHead mz mo z o width) x earlier b hn h5 k
  dsimp only at ht
  change run (nonemptyHead mz mo z o width) (5,scannedTape x (earlier++[b])) k = _ at h
  unfold scannedTape at h
  rw [h] at ht
  simpa [program,Shared.Codes.FiniteProgramPairDispatch.tm2Program,shiftStatus,scannedTape] using ht

/-- Any full run of the empty initializer transfers to the unified table
with exactly two extra dispatcher transitions. -/
theorem transfer_empty (mz mo z o x : List Bool) (width k : Nat) (d : Config)
    (h : run (emptyHead mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
      ((BitstringEncoding.bitEncode (x,([] : List Bool))).length+1+k) = some (.inr d)) :
    run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
      ((BitstringEncoding.bitEncode (x,([] : List Bool))).length+1+2+k) =
        some (.inr (shiftConfig (8+(nonemptyHead mz mo z o width).length) d)) := by
  have hs := empty_head_scan mz mo z o x [] width
  dsimp only at hs
  rw [run_continue _ _ _ _ _ hs] at h
  have he := Shared.Codes.FiniteProgramEmptyWitnessHead.program_valid mz mo z o width
  have h5 : 5 < (emptyHead mz mo z o width).length := by
    rw [Shared.Codes.FiniteProgramEmptyWitnessHead.program_length]; omega
  have ht := Shared.Codes.FiniteProgramPairDispatch.run_empty_after_scan
    (nonemptyHead mz mo z o width) (emptyHead mz mo z o width) x he h5 k
  dsimp only at ht
  change run (emptyHead mz mo z o width) (5,scannedTape x []) k = _ at h
  unfold scannedTape at h
  rw [h] at ht
  simpa [program,Shared.Codes.FiniteProgramPairDispatch.tm2Program,shiftStatus,scannedTape] using ht


/-- The unified table initializes an empty-witness pair, including an empty
    first component, and incurs exactly two dispatch transitions. -/
theorem run_empty (mz mo z o x : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
    let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
      Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
    let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
        (total+2) = some (.inr d) ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,([] : List Bool))
  let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
  let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
  let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  obtain ⟨d,hr,_,ht⟩ := Shared.Codes.FiniteProgramEmptyWitnessHead.run_empty_head mz mo z o x width hm hz ho
  change run (emptyHead mz mo z o width) (initial input) total = some (.inr d) at hr
  have hle : input.length+1 ≤ total := by
    dsimp [input,total,sc,Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost]
    omega
  let k := total-(input.length+1)
  have hk : input.length+1+k = total := by dsimp [k]; omega
  have hr' : run (emptyHead mz mo z o width) (initial input) (input.length+1+k) = some (.inr d) := by
    rw [hk]; exact hr
  have h := transfer_empty mz mo z o x width k d hr'
  have htime : input.length+1+2+k = total+2 := by omega
  rw [htime] at h
  exact ⟨shiftConfig (8+(nonemptyHead mz mo z o width).length) d,h,ht⟩

/-- The unified table initializes every nonempty-witness pair with the same
    two-transition dispatch overhead. -/
theorem run_nonempty (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
    let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
      Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
    let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
        (total+2) = some (.inr d) ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,earlier++[b])
  let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
  let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
    Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
  let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  obtain ⟨d,hr,_,ht⟩ := Shared.Codes.FiniteProgramPairHeadAll.run_pair_head mz mo z o x earlier width b hm hz ho
  change run (nonemptyHead mz mo z o width) (initial input) total = some (.inr d) at hr
  have hle : input.length+1 ≤ total := by
    dsimp [input,total,sc,Shared.Codes.FiniteProgramPairDecodeAll.scanCost]
    omega
  let k := total-(input.length+1)
  have hk : input.length+1+k = total := by dsimp [k]; omega
  have hr' : run (nonemptyHead mz mo z o width) (initial input) (input.length+1+k) = some (.inr d) := by
    rw [hk]; exact hr
  have h := transfer_nonempty mz mo z o x earlier width b k d hr'
  have htime : input.length+1+2+k = total+2 := by omega
  rw [htime] at h
  exact ⟨shiftConfig 8 d,h,ht⟩



/-- The two branch-specific terminal rows of the unified initializer. -/
def nonemptyExit (mz mo z o : List Bool) (width : Nat) : Nat :=
  8+(Shared.Codes.FiniteProgramPairHeadAll.handoffPre mz mo z o width).length+14

def emptyExit (mz mo z o : List Bool) (width : Nat) : Nat :=
  8+(nonemptyHead mz mo z o width).length+
    (Shared.Codes.FiniteProgramEmptyWitnessHead.handoffPre mz mo z o width).length+14

theorem run_empty_at_exit (mz mo z o x : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
    let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
      Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
    let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
        (total+2) = some (.inr d) ∧ d.1 = emptyExit mz mo z o width ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,([] : List Bool))
  let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
  let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
  let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  obtain ⟨d,hr,hd,ht⟩ := Shared.Codes.FiniteProgramEmptyWitnessHead.run_empty_head mz mo z o x width hm hz ho
  change run (emptyHead mz mo z o width) (initial input) total = some (.inr d) at hr
  have hle : input.length+1 ≤ total := by
    dsimp [input,total,sc,Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost]
    omega
  let k := total-(input.length+1)
  have hk : input.length+1+k = total := by dsimp [k]; omega
  have hr' : run (emptyHead mz mo z o width) (initial input) (input.length+1+k) = some (.inr d) := by
    rw [hk]; exact hr
  have h := transfer_empty mz mo z o x width k d hr'
  have htime : input.length+1+2+k = total+2 := by omega
  rw [htime] at h
  refine ⟨shiftConfig (8+(nonemptyHead mz mo z o width).length) d,h,?_,ht⟩
  simp [shiftConfig,emptyExit,hd,Nat.add_assoc]

theorem run_nonempty_at_exit (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
    let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
      Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
    let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
        (total+2) = some (.inr d) ∧ d.1 = nonemptyExit mz mo z o width ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let input := BitstringEncoding.bitEncode (x,earlier++[b])
  let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
  let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
    Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
  let total := sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  obtain ⟨d,hr,hd,ht⟩ := Shared.Codes.FiniteProgramPairHeadAll.run_pair_head mz mo z o x earlier width b hm hz ho
  change run (nonemptyHead mz mo z o width) (initial input) total = some (.inr d) at hr
  have hle : input.length+1 ≤ total := by
    dsimp [input,total,sc,Shared.Codes.FiniteProgramPairDecodeAll.scanCost]
    omega
  let k := total-(input.length+1)
  have hk : input.length+1+k = total := by dsimp [k]; omega
  have hr' : run (nonemptyHead mz mo z o width) (initial input) (input.length+1+k) = some (.inr d) := by
    rw [hk]; exact hr
  have h := transfer_nonempty mz mo z o x earlier width b k d hr'
  have htime : input.length+1+2+k = total+2 := by omega
  rw [htime] at h
  refine ⟨shiftConfig 8 d,h,?_,ht⟩
  simp [shiftConfig,nonemptyExit,hd,Nat.add_assoc]


def emptyTime (mz mo z o x : List Bool) (width : Nat) : Nat :=
  let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
  Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width + 2 +
      (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)

def nonemptyTime (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool) : Nat :=
  let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
  Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
    Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b + 2 +
      (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)

def runtime (mz mo z o x w : List Bool) (width : Nat) : Nat :=
  match w.reverse with
  | [] => emptyTime mz mo z o x width + 2
  | b::tail => nonemptyTime mz mo z o x tail.reverse width b + 2

def emptyBound (mz z o x : List Bool) (width : Nat) : Nat :=
  let n := 6*x.length
  let k := (n+1)*width
  Shared.Codes.FiniteProgramEmptyWitnessDecode.scanBound mz z o x + 2 +
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeBound width n + 2 + (k*(20*k+21)+6) + 2

def nonemptyBound (mz z o x earlier : List Bool) (width : Nat) : Nat :=
  let n := 6*x.length+3*earlier.length+3
  let k := (n+1)*width
  Shared.Codes.FiniteProgramPairDecodeAll.scanBound mz z o x earlier + 2 +
    Shared.Codes.FiniteProgramPairDecodeAll.decodeBound width n + 2 + (k*(20*k+21)+6) + 2

def bound (mz z o x w : List Bool) (width : Nat) : Nat :=
  match w.reverse with
  | [] => emptyBound mz z o x width
  | _::tail => nonemptyBound mz z o x tail.reverse width

theorem runtime_bound (mz mo z o x w : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    runtime mz mo z o x w width ≤ bound mz z o x w width := by
  cases hw : w.reverse with
  | nil =>
    simp only [runtime,bound,hw]
    have h := Shared.Codes.FiniteProgramEmptyWitnessHead.total_cost_bound mz mo z o x width hm hz ho
    change emptyTime mz mo z o x width + 2 ≤ emptyBound mz z o x width
    dsimp [emptyTime,emptyBound] at *
    omega
  | cons b tail =>
    simp only [runtime,bound,hw]
    have h := Shared.Codes.FiniteProgramPairHeadAll.total_cost_bound mz mo z o x tail.reverse width b hm hz ho
    change nonemptyTime mz mo z o x tail.reverse width b + 2 ≤ nonemptyBound mz z o x tail.reverse width
    dsimp [nonemptyTime,nonemptyBound] at *
    omega

/-- The same valid finite table initializes every canonical encoded pair;
    its exact transition count is the executable `runtime`. -/
theorem run_tm2_all (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x w : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let words := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,w)).map inp.symm)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w)))
        (runtime mz mo z o x w width) = some (.inr d) ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  have hm : mz.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false
  have hz : z.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false
  have ho : o.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true
  cases w using List.reverseRecOn with
  | nil =>
    have h := run_empty mz mo z o x width hm hz ho
    have hw : Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
          ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm) := by
      have hrev : ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm).reverse =
          inp.symm false :: (Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits x).map inp.symm := by
        rw [← List.map_reverse,Shared.Codes.FiniteProgramEmptyWitness.pair_reverse]; rfl
      rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
      have hs : Shared.ComplexityBridge.FirstBlocksContent.selected z o =
          Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
        funext bit; cases bit <;> rfl
      simp only [Shared.Codes.FiniteProgramEmptyWitnessDecode.words,hs,List.flatMap_map]
      rfl
    obtain ⟨d,hr,ht⟩ := h
    refine ⟨d,?_,?_⟩
    · simpa only [runtime,List.reverse_nil,emptyTime] using hr
    · rw [← hw]; exact ht
  | append_singleton earlier b =>
    have h := run_nonempty mz mo z o x earlier width b hm hz ho
    have hw : Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
          ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
      change mz ++ (Shared.Codes.FiniteProgramPairDecodeAll.restBits x earlier b).flatMap
        (Shared.ComplexityBridge.FirstBlocksContent.selected z o) = _
      have hs : Shared.ComplexityBridge.FirstBlocksContent.selected z o =
          Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
        funext bit; cases bit <;> rfl
      rw [hs]
      exact (Shared.Codes.FiniteProgramMarkedWitness.tm2_pair_words tm enc inp x earlier b).symm
    obtain ⟨d,hr,ht⟩ := h
    refine ⟨d,?_,?_⟩
    · simpa only [runtime,List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.nil_append,List.cons_append,List.reverse_reverse,nonemptyTime] using hr
    · rw [← hw]; exact ht


theorem run_tm2_all_at_exit (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x w : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let words := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,w)).map inp.symm)
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,w)))
        (runtime mz mo z o x w width) = some (.inr d) ∧
      (d.1 = nonemptyExit mz mo z o width ∨ d.1 = emptyExit mz mo z o width) ∧
      TapeRel d.2 (initial words).2 := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  have hm : mz.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false
  have hz : z.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false
  have ho : o.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true
  cases w using List.reverseRecOn with
  | nil =>
    have h := run_empty_at_exit mz mo z o x width hm hz ho
    have hw : Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
          ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm) := by
      have hrev : ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm).reverse =
          inp.symm false :: (Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits x).map inp.symm := by
        rw [← List.map_reverse,Shared.Codes.FiniteProgramEmptyWitness.pair_reverse]; rfl
      rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
      have hs : Shared.ComplexityBridge.FirstBlocksContent.selected z o =
          Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
        funext bit; cases bit <;> rfl
      simp only [Shared.Codes.FiniteProgramEmptyWitnessDecode.words,hs,List.flatMap_map]
      rfl
    obtain ⟨d,hr,hstate,ht⟩ := h
    refine ⟨d,?_,Or.inr hstate,?_⟩
    · simpa only [runtime,List.reverse_nil,emptyTime] using hr
    · rw [← hw]; exact ht
  | append_singleton earlier b =>
    have h := run_nonempty_at_exit mz mo z o x earlier width b hm hz ho
    have hw : Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
          ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
      change mz ++ (Shared.Codes.FiniteProgramPairDecodeAll.restBits x earlier b).flatMap
        (Shared.ComplexityBridge.FirstBlocksContent.selected z o) = _
      have hs : Shared.ComplexityBridge.FirstBlocksContent.selected z o =
          Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
        funext bit; cases bit <;> rfl
      rw [hs]
      exact (Shared.Codes.FiniteProgramMarkedWitness.tm2_pair_words tm enc inp x earlier b).symm
    obtain ⟨d,hr,hstate,ht⟩ := h
    refine ⟨d,?_,Or.inl hstate,?_⟩
    · simpa only [runtime,List.reverse_append,List.reverse_cons,List.reverse_nil,
        List.nil_append,List.cons_append,List.reverse_reverse,nonemptyTime] using hr
    · rw [← hw]; exact ht

namespace Fixtures
example : ∃ d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))
    (runtime [] [] [] [] [] [] 0) = some (.inr d) := by
  obtain ⟨d,h,_⟩ := run_empty [] [] [] [] [] 0 rfl rfl rfl
  exact ⟨d,h⟩
example : ∃ d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([] : List Bool),[true])))
    (runtime [] [] [] [] [] [true] 0) = some (.inr d) := by
  obtain ⟨d,h,_⟩ := run_nonempty [] [] [] [] [] [] 0 true rfl rfl rfl
  exact ⟨d,h⟩
end Fixtures

end Shared.Codes.FiniteProgramPairUnified

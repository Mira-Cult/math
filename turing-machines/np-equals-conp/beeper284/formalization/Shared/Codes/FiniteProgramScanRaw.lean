import Shared.Codes.FiniteProgramScanDecode
import Shared.Codes.FiniteProgramUntag

/-! Connect the nonempty first-block scan/decoder to the finite raw-bit
untagger. The run begins from a phase-aligned tape, not from raw input. -/
namespace Shared.Codes.FiniteProgramScanRaw
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus step_shift run_shift)
open Shared.Codes.FiniteProgramSplice (stem stem_length)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems totalCost padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (selected rawBlocks)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base (zero one : List Bool) (width : Nat) := Shared.Codes.FiniteProgramScanDecode.program zero one width

def stop (zero one : List Bool) (width : Nat) : Nat :=
  (Shared.Codes.FiniteProgramScanDecode.handoffPre zero one).length+47+empty width

theorem probe_zero_empty (t : Tape) :
    step Shared.Codes.FiniteProgramFrameProbe.base (53,t) = some (.inl false) := by
  have hr : Shared.Codes.FiniteProgramFrameProbe.base[53]? = some Shared.Codes.FiniteProgramFrameProbe.dummy := by
    simp [Shared.Codes.FiniteProgramFrameProbe.base,link,Shared.Codes.FiniteProgramFrameProbe.pre,
      Shared.Codes.FiniteProgramDropTag.program_length]
  cases h : t.2.1 <;> simp [step,hr,Shared.Codes.FiniteProgramFrameProbe.dummy,h]

theorem probe_empty (n : Nat) (t : Tape) :
    step (Shared.Codes.FiniteProgramFrameProbe.program n) (8*n+53,t) = some (.inl false) := by
  induction n with
  | zero => exact probe_zero_empty t
  | succ n ih =>
    have h := step_shift (stem Shared.Codes.FiniteProgramCrossTag.phase)
      (Shared.Codes.FiniteProgramFrameProbe.program n) [] (8*n+53,t)
      (by simp [Shared.Codes.FiniteProgramFrameProbe.program_length])
    rw [ih] at h
    simpa [Shared.Codes.FiniteProgramFrameProbe.program,Shared.Codes.FiniteProgramSplice.program,
      stem_length,Shared.Codes.FiniteProgramCrossTag.phase,shiftConfig,shiftStatus,
      Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem loop_empty (n : Nat) (t : Tape) :
    step (Shared.Codes.FiniteProgramFrameLoop.program n) (empty n,t) = some (.inl false) := by
  have hs := probe_empty n t
  have hb : empty n < (Shared.Codes.FiniteProgramFrameLoop.base n).length := by
    simp [empty,Shared.Codes.FiniteProgramFrameLoop.base_length]
  have hn : empty n ≠ Shared.Codes.FiniteProgramFrameLoop.stop n := by
    simp [empty,Shared.Codes.FiniteProgramFrameLoop.stop]
  have h := Shared.Codes.FiniteProgramFrameLoop.base_other n (empty n,t) hb hn
  rw [← h]
  simpa [empty,Shared.Codes.FiniteProgramFrameLoop.base] using hs

theorem frame_start_empty (n : Nat) (t : Tape) :
    step (Shared.Codes.FiniteProgramFrameStart.program n) (47+empty n,t) = some (.inl false) := by
  have hc : ((empty n,t) : Config).1 < (Shared.Codes.FiniteProgramFrameLoop.program n).length := by
    simp [empty,Shared.Codes.FiniteProgramFrameLoop.length]
  have h := step_shift (stem Shared.Codes.FiniteProgramDropTag.program)
    (Shared.Codes.FiniteProgramFrameLoop.program n) [] (empty n,t) hc
  rw [loop_empty n t] at h
  simpa [Shared.Codes.FiniteProgramFrameStart.program,Shared.Codes.FiniteProgramSplice.program,
    stem_length,Shared.Codes.FiniteProgramDropTag.program_length,shiftConfig,shiftStatus] using h

theorem base_stop (zero one : List Bool) (width : Nat) (t : Tape) :
    step (base zero one width) (stop zero one width,t) = some (.inl false) := by
  have hc : ((47+empty width,t) : Config).1 < (Shared.Codes.FiniteProgramFrameStart.program width).length := by
    simp [empty,Shared.Codes.FiniteProgramFrameStart.program_length]; omega
  have h := step_shift (Shared.Codes.FiniteProgramScanDecode.handoffPre zero one)
    (Shared.Codes.FiniteProgramFrameStart.program width) [] (47+empty width,t) hc
  rw [frame_start_empty width t] at h
  simpa [base,stop,Shared.Codes.FiniteProgramScanDecode.program,shiftConfig,shiftStatus,Nat.add_assoc] using h

theorem stop_bound (zero one : List Bool) (width : Nat) : stop zero one width < (base zero one width).length := by
  simp [stop,empty,base,Shared.Codes.FiniteProgramScanDecode.program,link,
    Shared.Codes.FiniteProgramScanDecode.handoffPre_length,Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

def handoffPre (zero one : List Bool) (width : Nat) : Program :=
  (base zero one width).set (stop zero one width) (branch (base zero one width).length) ++
    [bridge ((base zero one width).length+1+11)]

def program (zero one : List Bool) (width : Nat) : Program :=
  link (handoffPre zero one width) Shared.Codes.FiniteProgramUntag.rewindProgram []

theorem handoffPre_length (zero one : List Bool) (width : Nat) :
    (handoffPre zero one width).length = (base zero one width).length+1 := by simp [handoffPre]

theorem program_length (zero one : List Bool) (width : Nat) :
    (program zero one width).length = 429+18*zero.length+18*one.length+8*width := by
  simp [program,link,handoffPre_length,base,Shared.Codes.FiniteProgramScanDecode.program_length,
    Shared.Codes.FiniteProgramUntag.rewindProgram_length]
  omega

theorem base_other (zero one : List Bool) (width : Nat) (d : Config)
    (hd : d.1 < (base zero one width).length) (hne : d.1 ≠ stop zero one width) :
    step (base zero one width) d = step (program zero one width) d := by
  have h : (program zero one width)[d.1]? = (base zero one width)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,h]

theorem stop_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[stop zero one width]? = some (branch (base zero one width).length) := by
  have hs := stop_bound zero one width
  simp [program,link,handoffPre,List.getElem?_append_left,hs]

theorem bridge_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[(base zero one width).length]? =
      some (bridge ((base zero one width).length+1+11)) := by
  simp [program,link,handoffPre]

/-- A charged right/left dispatch preserves the tape and enters the
untagger's rewind state 11. -/
theorem handoff (zero one : List Bool) (width : Nat) (b : Bool) (L R : List Bool) :
    run (program zero one width) (stop zero one width,tapeAt L (b::false::R)) 2 =
      some (.inr ((handoffPre zero one width).length+11,tapeAt L (b::false::R))) := by
  have hs := stop_row zero one width
  have hb := bridge_row zero one width
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (zero one : List Bool) (width : Nat) : valid (program zero one width) = true := by
  let s := base zero one width
  let d := Shared.Codes.FiniteProgramUntag.rewindProgram
  let k := s.length+1
  let m := k+d.length
  have hl : (program zero one width).length = m := by simp [program,link,handoffPre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramScanDecode.program_valid zero one width
    change valid s = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramUntag.rewindProgram_valid
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 11 < d.length := by simp [d,Shared.Codes.FiniteProgramUntag.rewindProgram_length]
  have hsm : s.length ≤ m := by dsimp [m,k]; omega
  have hbranch : validRow m (branch s.length).1 = true ∧ validRow m (branch s.length).2 = true := by
    have hlt : s.length < m := by dsimp [m,k]; omega
    simp [branch,validRow,hlt]
  have hbridge : validRow m (bridge (k+11)).1 = true ∧ validRow m (bridge (k+11)).2 = true := by
    have hlt : k+11 < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have hall : (program zero one width).all
      (fun r => validRow (program zero one width).length r.1 &&
        validRow (program zero one width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ s.set (stop zero one width) (branch s.length) ∨ r = bridge (k+11) ∨
        r ∈ d.map (shiftPair k) := by
      simpa [program,link,handoffPre,handoffPre_length,s,d,k,List.mem_append] using hr
    rw [hl]
    rcases hr' with hset | hbridge' | hmap
    · rcases List.mem_or_eq_of_mem_set hset with ho | he
      · obtain ⟨h₁,h₂⟩ := hs r ho
        simp only [Bool.and_eq_true]
        exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hsm h₁,
          Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hsm h₂⟩
      · subst r; simpa only [Bool.and_eq_true] using hbranch
    · subst r; simpa only [Bool.and_eq_true] using hbridge
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 k d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 k d.length h₂⟩
  have hn : (program zero one width).isEmpty = false := by
    cases h : program zero one width with
    | nil => simp [h] at hl; dsimp [m,k] at hl; omega
    | cons r rs => rfl
  change (!(program zero one width).isEmpty && (program zero one width).all
    (fun r => validRow (program zero one width).length r.1 &&
      validRow (program zero one width).length r.2)) = true
  rw [hn,hall]
  rfl

def rawCost : List Bool → Nat
  | [] => 4
  | x::xs => 3*(x::xs).length+1+(1+(10*xs.length+11+Shared.Codes.FiniteProgramUntag.cost xs))

def rawState : List Bool → Nat
  | [] => 22
  | _::_ => 49

def rawTape (L R : List Bool) : List Bool → Tape
  | [] => tapeAt (false::L) (false::false::R)
  | x::xs => tapeAt (Shared.Codes.FiniteProgramUntag.cursor x (false::false::L) xs).2
      ((Shared.Codes.FiniteProgramUntag.cursor x (false::false::L) xs).1::false::false::
        Shared.Codes.FiniteProgramUntag.padding xs.length (false::R))

/-- After a nonempty untagging run, the head and left tape contain exactly
the raw word in reverse tape-list order, followed by the source cells. -/
theorem raw_contents (x : Bool) (xs L R : List Bool) :
    (rawTape L R (x::xs)).2.1 :: (rawTape L R (x::xs)).1 =
      (x::xs).reverse ++ false::false::L := by
  have h := Shared.Codes.FiniteProgramUntag.cursor_contents x (false::false::L) xs
  simpa [rawTape,tapeAt,List.reverse_cons,List.append_assoc] using h

theorem untag_words (words L R : List Bool) :
    run Shared.Codes.FiniteProgramUntag.rewindProgram
      (11,tapeAt (cursor false (false::L) words).2 ((cursor false (false::L) words).1::false::R))
      (rawCost words) = some (.inr (rawState words,rawTape L R words)) := by
  cases words with
  | nil => simpa [rawCost,rawState,rawTape] using Shared.Codes.FiniteProgramUntag.untag_frame_cursor_empty L R
  | cons x xs => simpa [rawCost,rawState,rawTape] using Shared.Codes.FiniteProgramUntag.untag_frame_cursor x xs L R

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (zero one : List Bool) (width : Nat) :
    link (handoffPre zero one width) Shared.Codes.FiniteProgramUntag.rewindProgram [] =
      program zero one width := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

set_option maxHeartbeats 3000000 in
set_option linter.constructorNameAsVariable false in
/-- A single finite table scans a nonempty phase-aligned first-component
buffer, removes its metadata, and converts the selected words to raw bits.
The exact time includes both two-transition handoffs. The empty-word case
is handled separately by the same table. -/
theorem scan_raw (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (bit : Bool) (todo L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
      (bit::todo).reverse [] L)) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let r := false::padding bits.length [false,false,false,false,false]
    let scanCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits))
    ∃ d, run (program zero one width) c (scanCost+2+rawCost words) = some (.inr d) ∧
      d.1 = (handoffPre zero one width).length+rawState words ∧ TapeRel d.2 (rawTape L r words) := by
  dsimp only
  let bits := true::bit::true::true::true::rawBlocks todo
  let words := selected zero one false ++ bits.flatMap (selected zero one)
  let r := false::padding bits.length [false,false,false,false,false]
  let source := tapeAt (cursor false (false::L) words).2 ((cursor false (false::L) words).1::false::r)
  let scanCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
    (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits))
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramScanDecode.scan_decode
    zero one width hzero hone bit todo L c hq ht
  have hc : c.1 < (base zero one width).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramScanDecode.program_valid zero one width)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (base zero one width) (program zero one width)
    c mid scanCost (stop zero one width) false (Shared.Codes.FiniteProgramScanDecode.program_valid zero one width)
    hc (base_stop zero one width) (base_other zero one width) hm
  have hsource : TapeRel mid.2 source := htape
  have htwo := handoff zero one width (cursor false (false::L) words).1
    (cursor false (false::L) words).2 r
  change run (program zero one width) (stop zero one width,source) 2 = _ at htwo
  have hrel : StatusRel (run (program zero one width) mid 2)
      (run (program zero one width) (stop zero one width,source) 2) :=
    run_related _ _ _ hstate hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hdec := untag_words words L r
  change run Shared.Codes.FiniteProgramUntag.rewindProgram (11,source) (rawCost words) =
    some (.inr (rawState words,rawTape L r words)) at hdec
  have hshift := run_shift (handoffPre zero one width) Shared.Codes.FiniteProgramUntag.rewindProgram []
    Shared.Codes.FiniteProgramUntag.rewindProgram_valid (11,source)
    (by simp [Shared.Codes.FiniteProgramUntag.rewindProgram_length]) (rawCost words)
  rw [hdec,program_link] at hshift
  have hshift' : run (program zero one width) ((handoffPre zero one width).length+11,source) (rawCost words) =
      some (.inr ((handoffPre zero one width).length+rawState words,rawTape L r words)) := by
    simpa only [shiftConfig,shiftStatus] using hshift
  have hrel' : StatusRel (run (program zero one width) after (rawCost words))
      (run (program zero one width) ((handoffPre zero one width).length+11,source) (rawCost words)) :=
    run_related _ _ _ hqafter htafter (rawCost words)
  rw [hshift'] at hrel'
  obtain ⟨d,hf,hqd,htd⟩ := status_live _ _ _ hrel'
  refine ⟨d,?_,hqd,htd⟩
  change run (program zero one width) c (scanCost+2+rawCost words) = _
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
  exact hf

/-- The rewinding and untagging stage has a uniform quadratic bound in the
number of raw output bits, including the empty case. -/
theorem rawCost_bound (words : List Bool) :
    rawCost words ≤ (words.length+1)*(20*(words.length+1)+40)+20 := by
  cases words with
  | nil => simp [rawCost]
  | cons x xs =>
    have h := Shared.Codes.FiniteProgramUntag.rewind_cost_bound x xs
    let n := xs.length
    let b := 20*(n+2)+40
    have hm : n*(20*n+21) ≤ n*b := Nat.mul_le_mul_left n (by dsimp [b]; omega)
    have he : 3*(n+1)+1+(1+(10*n+11+4)) ≤ 2*b+20 := by dsimp [b]; omega
    change 3*(n+1)+1+(1+(10*n+11+Shared.Codes.FiniteProgramUntag.cost xs)) ≤ (n+2)*b+20
    calc
      _ ≤ 3*(n+1)+1+(1+(10*n+11+(n*(20*n+21)+4))) := by simpa [n] using h
      _ ≤ 3*(n+1)+1+(1+(10*n+11+(n*b+4))) := by omega
      _ ≤ (n+2)*b+20 := by rw [Nat.add_mul]; omega

theorem rawBlocks_length (todo : List Bool) : (rawBlocks todo).length = 6*todo.length := by
  induction todo with
  | nil => rfl
  | cons b todo ih =>
    change ([false,true,b,true,true,true] ++ rawBlocks todo).length = 6*(todo.length+1)
    simp only [List.length_append,List.length_cons,List.length_nil,ih,Nat.mul_add]
    omega

theorem selected_words_length (zero one bits : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) :
    (bits.flatMap (selected zero one)).length = bits.length*width := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    simp only [List.flatMap_cons,List.length_append,
      Shared.ComplexityBridge.FirstBlocksContent.selected_length zero one width hzero hone b,
      List.length_cons,ih,Nat.succ_mul]
    omega

/-- The untagger's bit count is linear in the number of first-component
blocks for each fixed codec width. -/
theorem output_words_length (zero one todo : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bit : Bool) :
    (selected zero one false ++
      (true::bit::true::true::true::rawBlocks todo).flatMap (selected zero one)).length =
      (6*(todo.length+1))*width := by
  let bits := true::bit::true::true::true::rawBlocks todo
  have hlen : bits.length+1 = 6*(todo.length+1) := by
    simp only [bits,List.length_cons,rawBlocks_length,Nat.mul_add]
  change (selected zero one false ++ bits.flatMap (selected zero one)).length = _
  rw [List.length_append,Shared.ComplexityBridge.FirstBlocksContent.selected_length zero one width hzero hone false,
    selected_words_length zero one bits width hzero hone]
  calc
    width+bits.length*width = (bits.length+1)*width := by simp [Nat.add_mul,Nat.add_comm]
    _ = _ := by rw [hlen]

/-- The complete run has an explicit sum of the scanner and decoder bounds,
two charged transitions, and the raw untagger's quadratic bound. -/
theorem scan_raw_cost_bound (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bit : Bool) (todo : List Bool) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let n := (bit::todo).length
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) +
      2+rawCost words ≤
    n*(6*(16*(n*gain+gain)+16*w+31)+4)+2+
      (30*(width+bits.length*(width+1))+20 + (bits.length+1)*
        (7*width+30*((bits.length+1)*(width+1))+26)) + 2+
      ((words.length+1)*(20*(words.length+1)+40)+20) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramScanDecode.scan_decode_cost_bound zero one width hzero hone bit todo
  dsimp only at hs
  have hu := rawCost_bound (selected zero one false ++
    (true::bit::true::true::true::rawBlocks todo).flatMap (selected zero one))
  omega

namespace Fixtures
example : (program [] [] 0).length = 429 := by simpa using program_length [] [] 0
example : valid (program [false] [true] 1) = true := program_valid [false] [true] 1
example : rawCost [] = 4 := rfl
example : (selected [false] [true] false ++
    (true::false::true::true::true::rawBlocks []).flatMap (selected [false] [true])).length = 6 := by decide
end Fixtures

end Shared.Codes.FiniteProgramScanRaw

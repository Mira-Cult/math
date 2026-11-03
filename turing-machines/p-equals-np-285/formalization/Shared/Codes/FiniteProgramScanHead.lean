import Shared.Codes.FiniteProgramScanRaw
import Shared.Codes.FiniteProgramMirror

/-! Connect the first-component scanner/decoder to the reflected untagger.
The result is a positioned raw word on a tape with explicit remaining cells. -/
namespace Shared.Codes.FiniteProgramScanHead
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems totalCost padding)
open Shared.ComplexityBridge.FirstBlocksContent (selected rawBlocks)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base (zero one : List Bool) (width : Nat) := Shared.Codes.FiniteProgramScanDecode.program zero one width
abbrev stop (zero one : List Bool) (width : Nat) := Shared.Codes.FiniteProgramScanRaw.stop zero one width

def handoffPre (zero one : List Bool) (width : Nat) : Program :=
  (base zero one width).set (stop zero one width) (branch (base zero one width).length) ++
    [bridge ((base zero one width).length+1)]

def program (zero one : List Bool) (width : Nat) : Program :=
  link (handoffPre zero one width) Shared.Codes.FiniteProgramMirror.positioned []

theorem handoffPre_length (zero one : List Bool) (width : Nat) :
    (handoffPre zero one width).length = (base zero one width).length+1 := by simp [handoffPre]

theorem program_length (zero one : List Bool) (width : Nat) :
    (program zero one width).length = 394+18*zero.length+18*one.length+8*width := by
  simp [program,link,handoffPre_length,base,Shared.Codes.FiniteProgramScanDecode.program_length,
    Shared.Codes.FiniteProgramMirror.positioned_length]
  omega

theorem base_other (zero one : List Bool) (width : Nat) (d : Config)
    (hd : d.1 < (base zero one width).length) (hne : d.1 ≠ stop zero one width) :
    step (base zero one width) d = step (program zero one width) d := by
  have h : (program zero one width)[d.1]? = (base zero one width)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,h]

theorem stop_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[stop zero one width]? = some (branch (base zero one width).length) := by
  have hs := Shared.Codes.FiniteProgramScanRaw.stop_bound zero one width
  simp [program,link,handoffPre,List.getElem?_append_left,hs]

theorem bridge_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[(base zero one width).length]? =
      some (bridge ((base zero one width).length+1)) := by
  simp [program,link,handoffPre]

theorem handoff (zero one : List Bool) (width : Nat) (b : Bool) (L R : List Bool) :
    run (program zero one width) (stop zero one width,tapeAt L (b::false::R)) 2 =
      some (.inr ((handoffPre zero one width).length,tapeAt L (b::false::R))) := by
  have hs := stop_row zero one width
  have hb := bridge_row zero one width
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (zero one : List Bool) (width : Nat) : valid (program zero one width) = true := by
  let s := base zero one width
  let d := Shared.Codes.FiniteProgramMirror.positioned
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
    have hv := Shared.Codes.FiniteProgramMirror.positioned_valid
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 0 < d.length := by simp [d,Shared.Codes.FiniteProgramMirror.positioned_length]
  have hsm : s.length ≤ m := by dsimp [m,k]; omega
  have hbranch : validRow m (branch s.length).1 = true ∧ validRow m (branch s.length).2 = true := by
    have hlt : s.length < m := by dsimp [m,k]; omega
    simp [branch,validRow,hlt]
  have hbridge : validRow m (bridge k).1 = true ∧ validRow m (bridge k).2 = true := by
    have hlt : k < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have hall : (program zero one width).all
      (fun r => validRow (program zero one width).length r.1 &&
        validRow (program zero one width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ s.set (stop zero one width) (branch s.length) ∨ r = bridge k ∨
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

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (zero one : List Bool) (width : Nat) :
    link (handoffPre zero one width) Shared.Codes.FiniteProgramMirror.positioned [] =
      program zero one width := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

set_option maxHeartbeats 3000000 in
set_option linter.constructorNameAsVariable false in
/-- A single finite table scans, removes metadata, converts to raw bits, and
positions the head on the first bit. The run starts at a nonempty, phase-
aligned first-component block and preserves other tape cells explicitly. -/
theorem scan_head (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (bit : Bool) (todo L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
      (bit::todo).reverse [] L)) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let r := padding bits.length [false,false,false,false,false]
    let result := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
      (words ++ false::r)
    let scanCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits))
    ∃ d, run (program zero one width) c
      (scanCost+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = some (.inr d) ∧
      d.1 = (handoffPre zero one width).length+14 ∧ TapeRel d.2 result := by
  dsimp only
  let bits := true::bit::true::true::true::rawBlocks todo
  let words := selected zero one false ++ bits.flatMap (selected zero one)
  let r := padding bits.length [false,false,false,false,false]
  let source := tapeAt (cursor false (false::L) words).2 ((cursor false (false::L) words).1::false::false::r)
  let result := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
    (words ++ false::r)
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
    hc (Shared.Codes.FiniteProgramScanRaw.base_stop zero one width) (base_other zero one width) hm
  have hsource : TapeRel mid.2 source := htape
  have htwo := handoff zero one width (cursor false (false::L) words).1
    (cursor false (false::L) words).2 (false::r)
  change run (program zero one width) (stop zero one width,source) 2 = _ at htwo
  have hrel : StatusRel (run (program zero one width) mid 2)
      (run (program zero one width) (stop zero one width,source) 2) :=
    run_related _ _ _ hstate hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hdec := Shared.Codes.FiniteProgramMirror.positioned_run words L r
  change run Shared.Codes.FiniteProgramMirror.positioned (0,source)
    (2+Shared.Codes.FiniteProgramUntag.cost words.reverse) = some (.inr (14,result)) at hdec
  have hshift := run_shift (handoffPre zero one width) Shared.Codes.FiniteProgramMirror.positioned []
    Shared.Codes.FiniteProgramMirror.positioned_valid (0,source)
    (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
    (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  rw [hdec,program_link] at hshift
  have hshift' : run (program zero one width) ((handoffPre zero one width).length,source)
      (2+Shared.Codes.FiniteProgramUntag.cost words.reverse) =
      some (.inr ((handoffPre zero one width).length+14,result)) := by
    simpa only [shiftConfig,shiftStatus,Nat.add_zero] using hshift
  have hrel' : StatusRel (run (program zero one width) after (2+Shared.Codes.FiniteProgramUntag.cost words.reverse))
      (run (program zero one width) ((handoffPre zero one width).length,source)
        (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) :=
    run_related _ _ _ hqafter htafter _
  rw [hshift'] at hrel'
  obtain ⟨d,hf,hqd,htd⟩ := status_live _ _ _ hrel'
  refine ⟨d,?_,hqd,htd⟩
  change run (program zero one width) c
    (scanCost+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = _
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
  exact hf

/-- The cost of the complete run is bounded by the previous scanner/decoder
bound, the two handoff steps, and the reflected untagger's quadratic bound. -/
theorem scan_head_cost_bound (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bit : Bool) (todo : List Bool) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let n := (bit::todo).length
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) +
      2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse) ≤
    n*(6*(16*(n*gain+gain)+16*w+31)+4)+2+
      (30*(width+bits.length*(width+1))+20 + (bits.length+1)*
        (7*width+30*((bits.length+1)*(width+1))+26)) + 2+
      (words.length*(20*words.length+21)+6) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramScanDecode.scan_decode_cost_bound zero one width hzero hone bit todo
  dsimp only at hs
  have hu := Shared.Codes.FiniteProgramMirror.positioned_cost_bound (selected zero one false ++
    (true::bit::true::true::true::rawBlocks todo).flatMap (selected zero one))
  omega

private theorem untag_padding_blank (n : Nat) (R : List Bool) (h : R.all (fun b => !b) = true) :
    (Shared.Codes.FiniteProgramUntag.padding n R).all (fun b => !b) = true := by
  induction n generalizing R with
  | zero => exact h
  | succ n ih =>
    simpa [Shared.Codes.FiniteProgramUntag.padding] using ih (false::false::R) (by simpa using h)

private theorem frame_padding_blank (n : Nat) (R : List Bool) (h : R.all (fun b => !b) = true) :
    (padding n R).all (fun b => !b) = true := by
  induction n generalizing R with
  | zero => exact h
  | succ n ih => simpa [padding] using ih (false::false::false::R) (by simpa using h)

private theorem all_false_eq_replicate (xs : List Bool) (h : xs.all (fun b => !b) = true) :
    xs = List.replicate xs.length false := by
  apply List.eq_replicate_length.mpr
  intro b hb
  have he := (List.all_eq_true.mp h) b hb
  cases b <;> simp_all

private theorem mk_blank (xs : List Bool) (h : xs.all (fun b => !b) = true) :
    Turing.ListBlank.mk xs = Turing.ListBlank.mk ([] : List Bool) := by
  have he := all_false_eq_replicate xs h
  apply Quotient.sound
  exact Or.inr ⟨xs.length,by simpa using he⟩

private theorem mk_append_blank (xs ys : List Bool) (h : ys.all (fun b => !b) = true) :
    Turing.ListBlank.mk (xs++ys) = Turing.ListBlank.mk xs := by
  have he := all_false_eq_replicate ys h
  apply Quotient.sound
  exact Or.inr ⟨ys.length,congrArg (fun suffix => xs++suffix) he⟩

/-- If the untouched left region was blank, the positioned result is the
finite evaluator's ordinary initial tape, including for an empty word. -/
theorem result_tape_initial (words : List Bool) (n : Nat) :
    TapeRel (tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length [false])
      (words ++ false::padding n [false,false,false,false,false])) (initial words).2 := by
  have hl : (false::false::Shared.Codes.FiniteProgramUntag.padding words.length [false]).all (fun b => !b) = true := by
    simpa using untag_padding_blank words.length [false] (by decide)
  have hr : (false::padding n [false,false,false,false,false]).all (fun b => !b) = true := by
    simpa using frame_padding_blank n [false,false,false,false,false] (by decide)
  cases words with
  | nil =>
    unfold TapeRel tapeAt initial
    simp only [List.nil_append,List.head?_cons,Option.getD_some,List.tail_cons]
    change (⟨false,Turing.ListBlank.mk _,Turing.ListBlank.mk _⟩ : Turing.Tape Bool) =
      ⟨false,Turing.ListBlank.mk [],Turing.ListBlank.mk []⟩
    rw [mk_blank _ hl,mk_blank _ (frame_padding_blank n [false,false,false,false,false] (by decide))]
  | cons b bs =>
    unfold TapeRel tapeAt initial
    simp only [List.cons_append,List.head?_cons,Option.getD_some,List.tail_cons]
    change (⟨b,Turing.ListBlank.mk _,Turing.ListBlank.mk _⟩ : Turing.Tape Bool) =
      ⟨b,Turing.ListBlank.mk [],Turing.ListBlank.mk bs⟩
    rw [mk_blank _ hl,mk_append_blank _ _ hr]

/-- Special case of `scan_head` when the untouched left region is blank:
the resulting tape is the evaluator's initial tape for the selected words.
This does not establish that an arbitrary original input reaches the
required phase-aligned configuration. -/
theorem scan_head_initial (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (bit : Bool) (todo : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
      (bit::todo).reverse [] [])) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let scanCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
      (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits))
    ∃ d, run (program zero one width) c
      (scanCost+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = some (.inr d) ∧
      d.1 = (handoffPre zero one width).length+14 ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  obtain ⟨d,hr,hstate,htape⟩ := scan_head zero one width hzero hone bit todo [] c hq ht
  refine ⟨d,hr,hstate,?_⟩
  exact Eq.trans htape (result_tape_initial _ _)

namespace Fixtures
example : (program [] [] 0).length = 394 := by simpa using program_length [] [] 0
example : valid (program [false] [true] 1) = true := program_valid [false] [true] 1
example : TapeRel (tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding 0 [false])
    ([] ++ false::padding 0 [false,false,false,false,false])) (initial []).2 := result_tape_initial [] 0
example : TapeRel (tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding 3 [false])
    ([false,true,false] ++ false::padding 2 [false,false,false,false,false]))
    (initial [false,true,false]).2 := result_tape_initial [false,true,false] 2
end Fixtures

end Shared.Codes.FiniteProgramScanHead

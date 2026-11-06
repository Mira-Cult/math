import Shared.Codes.FiniteProgramFrameStart

/-! Splice the nonempty first-block scanner to the framed-buffer decoder.
The proof starts from the scanner's phase-aligned tape, not a blank tape. -/
namespace Shared.Codes.FiniteProgramScanDecode
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems totalCost padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (selected rawBlocks)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev scanner (zero one : List Bool) := Shared.Codes.FiniteProgramFirstBlocksController.program zero one
abbrev boundary (zero one : List Bool) := Shared.Codes.FiniteProgramFirstBlocksController.boundary zero one

def handoffPre (zero one : List Bool) : Program :=
  (scanner zero one).set (boundary zero one) (branch (scanner zero one).length) ++
    [bridge ((scanner zero one).length+1)]

def program (zero one : List Bool) (width : Nat) : Program :=
  link (handoffPre zero one) (Shared.Codes.FiniteProgramFrameStart.program width) []

theorem handoffPre_length (zero one : List Bool) : (handoffPre zero one).length = (scanner zero one).length+1 := by
  simp [handoffPre]

theorem program_length (zero one : List Bool) (width : Nat) :
    (program zero one width).length = 348+18*zero.length+18*one.length+8*width := by
  simp [program,link,handoffPre_length,Shared.Codes.FiniteProgramFirstBlocksController.program_length,
    Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

theorem boundary_bound (zero one : List Bool) : boundary zero one < (scanner zero one).length := by
  simp [boundary,scanner,Shared.Codes.FiniteProgramFirstBlocksController.boundary,
    Shared.Codes.FiniteProgramFirstBlocksController.program,
    Shared.Codes.FiniteProgramFirstBlocksController.base_length]

theorem scanner_boundary (zero one : List Bool) (t : Tape) :
    step (scanner zero one) (boundary zero one,t) = some (.inl false) := by
  let phase := Shared.Codes.FiniteProgramFirstBlocksController.base zero one
  let stop := boundary zero one
  have hc : ((2,t) : Config).1 < Shared.Codes.FiniteProgramPhaseProbe.probe.length := by
    simp [Shared.Codes.FiniteProgramPhaseProbe.probe,Shared.Codes.FiniteProgramFirstBlockProbe.program]
  have h := Shared.Codes.FiniteProgramPhaseProbe.probe_segment zero one 6 (2,t) hc 1
  have hp : run Shared.Codes.FiniteProgramPhaseProbe.probe (2,t) 1 = some (.inl false) := by
    cases ht : t.2.1 <;> simp [run,advance,step,Shared.Codes.FiniteProgramPhaseProbe.probe,
      Shared.Codes.FiniteProgramFirstBlockProbe.program,Shared.Codes.FiniteProgramPhaseProbe.dummy,ht]
  rw [hp] at h
  have hb : step phase (stop,t) = some (.inl false) := by
    simpa [phase,stop,boundary,Shared.Codes.FiniteProgramFirstBlocksController.base,
      Shared.Codes.FiniteProgramFirstBlocksController.boundary,shiftConfig,shiftStatus,run,advance] using h
  have hdiff : stop ≠ Shared.Codes.FiniteProgramFirstBlocksController.interior zero one := by
    simp [stop,Shared.Codes.FiniteProgramFirstBlocksController.boundary,
      Shared.Codes.FiniteProgramFirstBlocksController.interior]
  have hbound : stop < phase.length := by
    simp [stop,phase,Shared.Codes.FiniteProgramFirstBlocksController.boundary,
      Shared.Codes.FiniteProgramFirstBlocksController.base_length]
  have he := Shared.Codes.FiniteProgramFirstBlocksController.base_other zero one (stop,t) hbound hdiff
  rw [← he]
  exact hb

theorem scanner_other (zero one : List Bool) (width : Nat) (d : Config)
    (hd : d.1 < (scanner zero one).length) (hne : d.1 ≠ boundary zero one) :
    step (scanner zero one) d = step (program zero one width) d := by
  have hl : (program zero one width)[d.1]? = (scanner zero one)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hl]

theorem boundary_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[boundary zero one]? = some (branch (scanner zero one).length) := by
  have hb := boundary_bound zero one
  simp [program,link,handoffPre,List.getElem?_append_left,hb]

theorem bridge_row (zero one : List Bool) (width : Nat) :
    (program zero one width)[(scanner zero one).length]? =
      some (bridge ((scanner zero one).length+1)) := by
  simp [program,link,handoffPre]

theorem handoff (zero one : List Bool) (width : Nat) (b : Bool) (L R : List Bool) :
    run (program zero one width) (boundary zero one,tapeAt L (b::false::R)) 2 =
      some (.inr ((handoffPre zero one).length,tapeAt L (b::false::R))) := by
  have hb := boundary_row zero one width
  have hc := bridge_row zero one width
  cases b <;> simp [run,advance,step,hb,hc,branch,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (zero one : List Bool) (width : Nat) : valid (program zero one width) = true := by
  let s := scanner zero one
  let d := Shared.Codes.FiniteProgramFrameStart.program width
  let k := s.length+1
  let m := k+d.length
  have hl : (program zero one width).length = m := by simp [program,link,handoffPre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one
    change valid s = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramFrameStart.program_valid width
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 0 < d.length := Shared.Codes.FiniteProgramLink.valid_nonempty d
    (Shared.Codes.FiniteProgramFrameStart.program_valid width)
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
    have hr' : r ∈ s.set (boundary zero one) (branch s.length) ∨ r = bridge k ∨
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
    link (handoffPre zero one) (Shared.Codes.FiniteProgramFrameStart.program width) [] =
      program zero one width := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

set_option maxHeartbeats 3000000 in
set_option linter.constructorNameAsVariable false in
/-- Run the actual scanner, its two-transition handoff, and the actual
decoder in one valid table. Initial and final tapes are related modulo blank
padding. This starts at a nonempty phase-aligned first-component block, not
at the original input boundary. -/
theorem scan_decode (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (bit : Bool) (todo L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
      (bit::todo).reverse [] L)) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let words := selected zero one false ++ bits.flatMap (selected zero one)
    let decodeCost := 30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)
    let finalTape := tapeAt (cursor false (false::L) words).2
      ((cursor false (false::L) words).1::false::false::padding bits.length [false,false,false,false,false])
    ∃ d, run (program zero one width) c
        (Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 + decodeCost) =
          some (.inr d) ∧
      d.1 = (handoffPre zero one).length+47+empty width ∧ TapeRel d.2 finalTape := by
  dsimp only
  let bits := true::bit::true::true::true::rawBlocks todo
  let words := selected zero one false ++ bits.flatMap (selected zero one)
  let buf := Shared.Codes.FiniteProgramFirstBlocksController.loopOutput zero one (bit::todo) []
  let source := tapeAt (false::L) (false::false::tagged buf ++ [false,false,false])
  let decodeCost := 30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)
  let finalTape := tapeAt (cursor false (false::L) words).2
    ((cursor false (false::L) words).1::false::false::padding bits.length [false,false,false,false,false])
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramFirstBlocksController.run_blocks
    zero one (bit::todo) [] L (by simp) c hq ht
  have hc : c.1 < (scanner zero one).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (scanner zero one) (program zero one width)
    c mid _ (boundary zero one) false (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one)
    hc (scanner_boundary zero one) (scanner_other zero one width) hm
  have hsource : TapeRel mid.2 source := by
    simpa [source,buf,Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape,
      Shared.ComplexityBridge.PairReverseFirst.expanded,tapeLeft,tapeAt,List.cons_append] using htape
  have htwo := handoff zero one width false (false::L) (tagged buf ++ [false,false,false])
  change run (program zero one width) (boundary zero one,source) 2 = _ at htwo
  have hrel : StatusRel (run (program zero one width) mid 2)
      (run (program zero one width) (boundary zero one,source) 2) :=
    run_related _ _ _ hstate hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hdec := Shared.Codes.FiniteProgramFrameStart.run_scan_buffer zero one width hzero hone
    bit false todo (false::L) [false,false]
  change run (Shared.Codes.FiniteProgramFrameStart.program width) (0,source) decodeCost =
    some (.inr (47+empty width,finalTape)) at hdec
  have hshift := run_shift (handoffPre zero one) (Shared.Codes.FiniteProgramFrameStart.program width) []
    (Shared.Codes.FiniteProgramFrameStart.program_valid width) (0,source)
    (by simp [Shared.Codes.FiniteProgramFrameStart.program_length]) decodeCost
  rw [hdec] at hshift
  rw [program_link] at hshift
  have hshift' : run (program zero one width) ((handoffPre zero one).length,source) decodeCost =
      some (.inr ((handoffPre zero one).length+47+empty width,finalTape)) := by
    simpa only [shiftConfig,shiftStatus,Nat.add_zero,Nat.add_assoc] using hshift
  have hrel' : StatusRel (run (program zero one width) after decodeCost)
      (run (program zero one width) ((handoffPre zero one).length,source) decodeCost) :=
    run_related _ _ _ hqafter htafter decodeCost
  rw [hshift'] at hrel'
  obtain ⟨d,hf,hqd,htd⟩ := status_live _ _ _ hrel'
  refine ⟨d,?_,hqd,htd⟩
  change run (program zero one width) c
    (Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 + decodeCost) = _
  rw [Nat.add_assoc]
  rw [run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
  exact hf

/-- The full charged run is bounded by the sum of the scanner's quadratic
bound, the two handoff transitions, and the decoder's quadratic bound. -/
theorem scan_decode_cost_bound (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bit : Bool) (todo : List Bool) :
    let bits := true::bit::true::true::true::rawBlocks todo
    let n := (bit::todo).length
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    Shared.Codes.FiniteProgramFirstBlocksController.loopCost zero one (bit::todo) [] + 2 +
        (30*(width+bits.length*(width+1))+20 + totalCost width (selectedItems zero one bits)) ≤
      n*(6*(16*(n*gain+gain)+16*w+31)+4)+2+
        (30*(width+bits.length*(width+1))+20 + (bits.length+1)*
          (7*width+30*((bits.length+1)*(width+1))+26)) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramFirstBlocksController.loopCost_bound zero one (bit::todo) []
  dsimp only at hs
  simp only [List.length_nil,Nat.zero_add] at hs
  have hd := Shared.Codes.FiniteProgramFrameStart.nonempty_cost_bound zero one width hzero hone
    (true::bit::true::true::true::rawBlocks todo)
  omega

namespace Fixtures
example : (program [] [] 0).length = 348 := by simpa using program_length [] [] 0
example : valid (program [false] [true] 1) = true := program_valid [false] [true] 1
example : run (program [] [] 0) (boundary [] [],tapeAt [] [false,false,false]) 2 =
    some (.inr ((handoffPre [] []).length,tapeAt [] [false,false,false])) := by
  exact handoff [] [] 0 false [] [false]
end Fixtures

end Shared.Codes.FiniteProgramScanDecode

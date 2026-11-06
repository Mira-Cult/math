import Shared.Codes.FiniteProgramSeparatorFirst
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Connect the nonempty witness loop to separator restoration and the
nonempty first-component loop. Entry assumes a phase-aligned witness buffer. -/
namespace Shared.Codes.FiniteProgramWitnessFirst
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev scanner := Shared.Codes.FiniteProgramWitnessController.program
abbrev boundary := Shared.Codes.FiniteProgramWitnessController.boundary
abbrev payload := Shared.Codes.FiniteProgramSeparatorFirst.program

def restoreRow (target : Nat) : Row × Row :=
  ((false,true,target,0),(false,true,target,0))
def handoffPre (zero one : List Bool) : Program :=
  (scanner zero one).set (boundary zero one) (restoreRow (scanner zero one).length) ++
    [bridge ((scanner zero one).length+1)]
def program (zero one : List Bool) : Program := link (handoffPre zero one) (payload zero one) []

theorem handoffPre_length (zero one : List Bool) : (handoffPre zero one).length = (scanner zero one).length+1 := by
  simp [handoffPre]

theorem boundary_bound (zero one : List Bool) : boundary zero one < (scanner zero one).length := by
  simp [boundary,scanner,Shared.Codes.FiniteProgramWitnessController.boundary,
    Shared.Codes.FiniteProgramWitnessController.program,
    Shared.Codes.FiniteProgramWitnessController.base_length]

theorem scanner_boundary (zero one : List Bool) (t : Tape) :
    step (scanner zero one) (boundary zero one,t) = some (.inl false) := by
  let phase := Shared.Codes.FiniteProgramWitnessController.base zero one
  let stop := boundary zero one
  have hc : ((4,t) : Config).1 < Shared.Codes.FiniteProgramWitnessPhases.probe.length := by
    simp [Shared.Codes.FiniteProgramWitnessPhases.probe]
  have h := Shared.Codes.FiniteProgramWitnessPhases.probe_segment zero one 3 (4,t) hc 1
  have hp : run Shared.Codes.FiniteProgramWitnessPhases.probe (4,t) 1 = some (.inl false) := by
    cases ht : t.2.1 <;> simp [run,advance,step,Shared.Codes.FiniteProgramWitnessPhases.probe,
      Shared.Codes.FiniteProgramWitnessPhases.dummy,ht]
  rw [hp] at h
  have hb : step phase (stop,t) = some (.inl false) := by
    simpa [phase,stop,boundary,Shared.Codes.FiniteProgramWitnessController.base,
      Shared.Codes.FiniteProgramWitnessController.boundary,shiftConfig,shiftStatus,run,advance] using h
  have hdiff : stop ≠ Shared.Codes.FiniteProgramWitnessController.interior zero one := by
    simp [stop,Shared.Codes.FiniteProgramWitnessController.boundary,
      Shared.Codes.FiniteProgramWitnessController.interior]
  have hbound : stop < phase.length := by
    simp [stop,phase,Shared.Codes.FiniteProgramWitnessController.boundary,
      Shared.Codes.FiniteProgramWitnessController.base_length]
  have he := Shared.Codes.FiniteProgramWitnessController.base_other zero one (stop,t) hbound hdiff
  rw [← he]
  exact hb

theorem scanner_other (zero one : List Bool) (d : Config)
    (hd : d.1 < (scanner zero one).length) (hne : d.1 ≠ boundary zero one) :
    step (scanner zero one) d = step (program zero one) d := by
  have hl : (program zero one)[d.1]? = (scanner zero one)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hl]

theorem boundary_row (zero one : List Bool) :
    (program zero one)[boundary zero one]? = some (restoreRow (scanner zero one).length) := by
  have hb := boundary_bound zero one
  simp [program,link,handoffPre,List.getElem?_append_left,hb]

theorem bridge_row (zero one : List Bool) :
    (program zero one)[(scanner zero one).length]? = some (bridge ((scanner zero one).length+1)) := by
  simp [program,link,handoffPre]

/-- Two charged moves erase the landmark and restore the original separator. -/
theorem restore_handoff (zero one : List Bool) (L R : List Bool) :
    run (program zero one) (boundary zero one,tapeAt L (true::false::R)) 2 =
      some (.inr ((handoffPre zero one).length,tapeAt L (false::false::R))) := by
  have hb := boundary_row zero one
  have hc := bridge_row zero one
  simp [run,advance,step,hb,hc,restoreRow,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (zero one : List Bool)  : valid (program zero one) = true := by
  let s := scanner zero one
  let d := Shared.Codes.FiniteProgramSeparatorFirst.program zero one
  let k := s.length+1
  let m := k+d.length
  have hl : (program zero one).length = m := by simp [program,link,handoffPre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramWitnessController.program_valid zero one
    change valid s = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramSeparatorFirst.program_valid zero one
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 0 < d.length := Shared.Codes.FiniteProgramLink.valid_nonempty d
    (Shared.Codes.FiniteProgramSeparatorFirst.program_valid zero one)
  have hsm : s.length ≤ m := by dsimp [m,k]; omega
  have hbranch : validRow m (restoreRow s.length).1 = true ∧ validRow m (restoreRow s.length).2 = true := by
    have hlt : s.length < m := by dsimp [m,k]; omega
    simp [restoreRow,validRow,hlt]
  have hbridge : validRow m (bridge k).1 = true ∧ validRow m (bridge k).2 = true := by
    have hlt : k < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have hall : (program zero one).all
      (fun r => validRow (program zero one).length r.1 &&
        validRow (program zero one).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ s.set (boundary zero one) (restoreRow s.length) ∨ r = bridge k ∨
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
  have hn : (program zero one).isEmpty = false := by
    cases h : program zero one with
    | nil => simp [h] at hl; dsimp [m,k] at hl; omega
    | cons r rs => rfl
  change (!(program zero one).isEmpty && (program zero one).all
    (fun r => validRow (program zero one).length r.1 &&
      validRow (program zero one).length r.2)) = true
  rw [hn,hall]
  rfl


theorem program_length (zero one : List Bool) :
    (program zero one).length = 412 + 30*zero.length + 30*one.length := by
  simp [program,link,handoffPre_length,Shared.Codes.FiniteProgramWitnessController.program_length,
    Shared.Codes.FiniteProgramSeparatorFirst.program_length]
  omega

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (zero one : List Bool) :
    link (handoffPre zero one) (payload zero one) [] = program zero one := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

/-- One valid finite table processes a nonempty aligned witness, restores the
separator in two charged moves, and processes the separator and nonempty
first component. The initial buffer may already contain data. -/
theorem run_witness_first (zero one todo x xs L : List Bool)
    (hw : todo ≠ []) (hx : x ≠ []) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape todo.reverse xs
      ((expanded x).reverse ++ false::false::L))) :
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
    ∃ d, run (program zero one) c
        (Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs + 2 +
          (cost zero one false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost zero one x.reverse
            (output zero one false buf))) = some (.inr d) ∧
      d.1 = (handoffPre zero one).length + Shared.Codes.FiniteProgramSeparatorFirst.offset zero one +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary zero one ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput zero one x.reverse (output zero one false buf)) L) := by
  dsimp only
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
  let left := (expanded x).reverse ++ false::false::L
  let marked := tapeAt left (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false])
  let restored := (canonical left false buf).2
  let wc := Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs
  let pc := cost zero one false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost zero one x.reverse
      (output zero one false buf)
  obtain ⟨mid,hm,hmid,htape⟩ := Shared.Codes.FiniteProgramWitnessController.run_blocks
    zero one todo xs left hw c hq ht
  have hmarked : Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] buf left = marked := by
    rfl
  rw [hmarked] at htape
  have hc : c.1 < (scanner zero one).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramWitnessController.program_valid zero one)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (scanner zero one) (program zero one)
    c mid wc (boundary zero one) false (Shared.Codes.FiniteProgramWitnessController.program_valid zero one)
    hc (scanner_boundary zero one) (scanner_other zero one) hm
  have hrestore := restore_handoff zero one left
    (Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false])
  change run (program zero one) (boundary zero one,marked) 2 =
    some (.inr ((handoffPre zero one).length,restored)) at hrestore
  have hrel := run_related (program zero one) mid (boundary zero one,marked) hmid htape 2
  rw [hrestore] at hrel
  obtain ⟨start,hstart,hstate,ht⟩ := status_live _ _ _ hrel
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramSeparatorFirst.run_separator_first
    zero one x buf L hx (0,start.2) rfl ht
  have hin : ((0,start.2) : Config).1 < (payload zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramSeparatorFirst.program_valid zero one)
  have hshift := run_shift (handoffPre zero one) (payload zero one) []
    (Shared.Codes.FiniteProgramSeparatorFirst.program_valid zero one) (0,start.2) hin pc
  rw [hlast] at hshift
  have hcfg := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state start (handoffPre zero one).length hstate
  refine ⟨shiftConfig (handoffPre zero one).length last,?_,?_,hlastt⟩
  · change run (program zero one) c ((wc+2)+pc) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hstart,hcfg]
    rw [program_link] at hshift
    simpa only [shiftStatus] using hshift
  · simp only [shiftConfig,hlastq]
    omega

/-- The witness loop grows the tagged buffer by at most one metadata bit and
one selected word per encoded witness bit. -/
theorem witness_buffer_length (zero one todo xs : List Bool) :
    (Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs).length ≤
      xs.length + todo.length * (3*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one)) := by
  induction todo generalizing xs with
  | nil => simp [Shared.Codes.FiniteProgramWitnessController.loopOutput]
  | cons b bs ih =>
    have hb := Shared.Codes.FiniteProgramWitnessController.groupOutput_length_le zero one b xs
    have hr := ih (Shared.Codes.FiniteProgramWitnessController.groupOutput zero one b xs)
    simp only [Shared.Codes.FiniteProgramWitnessController.loopOutput,List.length_cons,Nat.add_mul] at ⊢
    omega

/-- Explicit polynomial bound for the complete witness-to-first-component
segment. It includes both restoration transitions. -/
theorem total_cost_bound (zero one todo x xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gainW := 3*(1+w)
    let gainX := 6*(1+w)
    let buffer := xs.length + todo.length*gainW
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
    Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs + 2 +
      (cost zero one false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost zero one x.reverse
        (output zero one false buf)) ≤
      todo.length*(3*(16*(xs.length+todo.length*gainW+gainW)+16*w+31)+4) + 2 +
      (16*buffer+16*w+31 +
        x.length*(6*(16*(buffer+1+w+x.length*gainX+gainX)+16*w+31)+4)) := by
  dsimp only
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
  let gainW := 3*(1+w)
  let gainX := 6*(1+w)
  let buffer := xs.length + todo.length*gainW
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
  have hbuf : buf.length ≤ buffer := by
    simpa [buf,buffer,gainW,w] using witness_buffer_length zero one todo xs
  have hword : zero.length ≤ w := by
    dsimp [w,Shared.Codes.FiniteProgramTaggedLoop.maxWord]
    exact Nat.le_max_left _ _
  have hout : (output zero one false buf).length ≤ buffer+1+w := by
    have h := Shared.Codes.FiniteProgramTaggedLoop.output_length_le zero one false buf
    change (output zero one false buf).length ≤ buf.length+1+w at h
    omega
  have hcost : cost zero one false buf ≤ 16*buffer+16*w+31 := by
    simp only [Shared.Codes.FiniteProgramTaggedLoop.cost,Bool.false_eq_true,reduceIte]
    omega
  have hw := Shared.Codes.FiniteProgramWitnessController.loopCost_bound zero one todo xs
  change Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs ≤
    todo.length*(3*(16*(xs.length+todo.length*gainW+gainW)+16*w+31)+4) at hw
  have hf := Shared.Codes.FiniteProgramFirstBlocksController.loopCost_bound zero one x.reverse
    (output zero one false buf)
  simp only [List.length_reverse] at hf
  have hf' : Shared.Codes.FiniteProgramSeparatorFirst.firstCost zero one x.reverse (output zero one false buf) ≤
      x.length*(6*(16*(buffer+1+w+x.length*gainX+gainX)+16*w+31)+4) := by
    apply le_trans hf
    apply Nat.mul_le_mul_left
    dsimp [gainX,w]
    omega
  exact Nat.add_le_add (Nat.add_le_add hw (Nat.le_refl 2)) (Nat.add_le_add hcost hf')

namespace Fixtures
example : run (program [] []) (boundary [] [],([],true,[false,false])) 2 =
    some (.inr ((handoffPre [] []).length,([],false,[false,false]))) := by
  simpa [tapeAt] using restore_handoff [] [] [] [false]
example : valid (program [false] [true]) = true := program_valid [false] [true]
example : (program [false] [true]).length = 472 := by simpa using program_length [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramWitnessFirst

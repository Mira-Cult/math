import Shared.Codes.FiniteProgramRelink
import Shared.Codes.FiniteProgramSeparatorFirstAll
import Shared.Codes.FiniteProgramWitnessFirst
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Connect a nonempty witness scan to the guarded first-component scan,
including the empty first-component case. -/
namespace Shared.Codes.FiniteProgramWitnessFirstAll
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev scanner := Shared.Codes.FiniteProgramWitnessController.program
abbrev boundary := Shared.Codes.FiniteProgramWitnessController.boundary
abbrev handoffPre := Shared.Codes.FiniteProgramWitnessFirst.handoffPre
abbrev payload := Shared.Codes.FiniteProgramSeparatorFirstAll.program

def program (zero one : List Bool) : Program := link (handoffPre zero one) (payload zero one) []

theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  apply Shared.Codes.FiniteProgramRelink.valid_relink (handoffPre zero one)
    (Shared.Codes.FiniteProgramSeparatorFirst.program zero one) (payload zero one)
  · exact Shared.Codes.FiniteProgramWitnessFirst.program_valid zero one
  · exact Shared.Codes.FiniteProgramSeparatorFirstAll.program_valid zero one
  · rw [Shared.Codes.FiniteProgramSeparatorFirst.program_length,
      Shared.Codes.FiniteProgramSeparatorFirstAll.program_length]
    omega

theorem program_length (zero one : List Bool) :
    (program zero one).length = 418+30*zero.length+30*one.length := by
  simp [program,link,Shared.Codes.FiniteProgramWitnessFirst.handoffPre_length,
    Shared.Codes.FiniteProgramWitnessController.program_length,
    Shared.Codes.FiniteProgramSeparatorFirstAll.program_length]
  omega

theorem scanner_other (zero one : List Bool) (d : Config)
    (hd : d.1 < (scanner zero one).length) (hne : d.1 ≠ boundary zero one) :
    step (scanner zero one) d = step (program zero one) d := by
  have hfirst := Shared.Codes.FiniteProgramWitnessFirst.scanner_other zero one d hd hne
  have hpre : d.1 < (handoffPre zero one).length := by
    rw [Shared.Codes.FiniteProgramWitnessFirst.handoffPre_length]
    change d.1 < (scanner zero one).length+1
    omega
  have hnext := Shared.Codes.FiniteProgramRelink.prefix_step (handoffPre zero one)
    (Shared.Codes.FiniteProgramSeparatorFirst.program zero one) (payload zero one) [] [] d hpre
  change step (Shared.Codes.FiniteProgramWitnessFirst.program zero one) d = step (program zero one) d at hnext
  exact hfirst.trans hnext

theorem boundary_row (zero one : List Bool) :
    (program zero one)[boundary zero one]? = some
      (Shared.Codes.FiniteProgramWitnessFirst.restoreRow (scanner zero one).length) := by
  have h := Shared.Codes.FiniteProgramWitnessFirst.boundary_bound zero one
  simp [program,link,Shared.Codes.FiniteProgramWitnessFirst.handoffPre,
    List.getElem?_append_left,h]

theorem bridge_row (zero one : List Bool) :
    (program zero one)[(scanner zero one).length]? = some (bridge ((scanner zero one).length+1)) := by
  simp [program,link,Shared.Codes.FiniteProgramWitnessFirst.handoffPre]

theorem restore_handoff (zero one : List Bool) (L R : List Bool) :
    run (program zero one) (boundary zero one,tapeAt L (true::false::R)) 2 =
      some (.inr ((handoffPre zero one).length,tapeAt L (false::false::R))) := by
  have hb := boundary_row zero one
  have hc := bridge_row zero one
  simp [run,advance,step,hb,hc,Shared.Codes.FiniteProgramWitnessFirst.restoreRow,
    bridge,tapeAt,moveTape,Shared.Codes.FiniteProgramWitnessFirst.handoffPre_length]

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (zero one : List Bool) : link (handoffPre zero one) (payload zero one) [] = program zero one := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program

/-- A nonempty witness and any first component, including empty, are scanned
in one table. The guard adds four charged transitions. -/
theorem run_witness_first (zero one todo x xs L : List Bool) (hw : todo ≠ [])
    (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape todo.reverse xs
      ((expanded x).reverse ++ false::false::L))) :
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
    ∃ d, run (program zero one) c
        (Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs + 2 +
          (cost zero one false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost zero one x.reverse
            (output zero one false buf)))) = some (.inr d) ∧
      d.1 = (handoffPre zero one).length + Shared.Codes.FiniteProgramSeparatorFirstAll.offset zero one +
        (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary zero one) ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirstAll.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirstAll.firstOutput zero one x.reverse (output zero one false buf)) L) := by
  dsimp only
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
  let left := (expanded x).reverse ++ false::false::L
  let marked := tapeAt left (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false])
  let restored := (canonical left false buf).2
  let wc := Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs
  let pc := cost zero one false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost zero one x.reverse
      (output zero one false buf))
  obtain ⟨mid,hm,hmid,htape⟩ := Shared.Codes.FiniteProgramWitnessController.run_blocks
    zero one todo xs left hw c hq ht
  have hmarked : Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] buf left = marked := rfl
  rw [hmarked] at htape
  have hc : c.1 < (scanner zero one).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramWitnessController.program_valid zero one)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (scanner zero one) (program zero one)
    c mid wc (boundary zero one) false (Shared.Codes.FiniteProgramWitnessController.program_valid zero one)
    hc (Shared.Codes.FiniteProgramWitnessFirst.scanner_boundary zero one) (scanner_other zero one) hm
  have hrestore := restore_handoff zero one left
    (Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false])
  change run (program zero one) (boundary zero one,marked) 2 =
    some (.inr ((handoffPre zero one).length,restored)) at hrestore
  have hrel := run_related (program zero one) mid (boundary zero one,marked) hmid htape 2
  rw [hrestore] at hrel
  obtain ⟨start,hstart,hstate,ht⟩ := status_live _ _ _ hrel
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramSeparatorFirstAll.run_separator_first
    zero one x buf L (0,start.2) rfl ht
  have hin : ((0,start.2) : Config).1 < (payload zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramSeparatorFirstAll.program_valid zero one)
  have hshift := run_shift (handoffPre zero one) (payload zero one) []
    (Shared.Codes.FiniteProgramSeparatorFirstAll.program_valid zero one) (0,start.2) hin pc
  rw [hlast] at hshift
  have hcfg := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state start (handoffPre zero one).length hstate
  refine ⟨shiftConfig (handoffPre zero one).length last,?_,?_,hlastt⟩
  · change run (program zero one) c ((wc+2)+pc) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hstart,hcfg]
    rw [program_link] at hshift
    simpa only [shiftStatus] using hshift
  · simp only [shiftConfig,hlastq]
    omega

/-- The empty-aware guard contributes four steps to the established
quadratic witness and first-component bound. -/
theorem total_cost_bound (zero one todo x xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gainW := 3*(1+w)
    let gainX := 6*(1+w)
    let buffer := xs.length + todo.length*gainW
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs
    Shared.Codes.FiniteProgramWitnessController.loopCost zero one todo xs + 2 +
      (cost zero one false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost zero one x.reverse
        (output zero one false buf))) ≤
      todo.length*(3*(16*(xs.length+todo.length*gainW+gainW)+16*w+31)+4) + 2 +
      (16*buffer+16*w+31 + (4+
        x.length*(6*(16*(buffer+1+w+x.length*gainX+gainX)+16*w+31)+4))) := by
  have h := Shared.Codes.FiniteProgramWitnessFirst.total_cost_bound zero one todo x xs
  dsimp only [Shared.Codes.FiniteProgramSeparatorFirst.firstCost,
    Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost] at h ⊢
  omega

namespace Fixtures
example : valid (program [false] [true]) = true := program_valid [false] [true]
example : (program [false] [true]).length = 478 := by simpa using program_length [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramWitnessFirstAll

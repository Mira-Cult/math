import Shared.Codes.FiniteProgramTaggedLoop
import Shared.Codes.FiniteProgramSplice

/-! One finite phase executes a buffer cycle and enters a terminal final row.
The row can be spliced with the next phase or a boundary probe. -/
namespace Shared.Codes.FiniteProgramPhase
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (base stop base_valid base_length stop_bound base_stop output cost)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))

def program (zero one : List Bool) : Program :=
  let loop := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  loop.set (base zero one).length (bridge (base zero one).length.succ) ++ [dummy]

theorem loop_length (zero one : List Bool) :
    (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length = (base zero one).length+1 := by
  simp [Shared.Codes.FiniteProgramTaggedLoop.program]

theorem length (zero one : List Bool) : (program zero one).length = (base zero one).length+2 := by
  simp [program,loop_length]

theorem base_other (zero one : List Bool) (d : Config) (hd : d.1 < (base zero one).length)
    (hne : d.1 ≠ stop zero one) : step (base zero one) d = step (program zero one) d := by
  rw [Shared.Codes.FiniteProgramTaggedLoop.base_other zero one d hd hne]
  have he : (program zero one)[d.1]? = (Shared.Codes.FiniteProgramTaggedLoop.program zero one)[d.1]? := by
    unfold program
    rw [List.getElem?_append_left (by simp [loop_length]; omega),List.getElem?_set_ne (by omega)]
  simp [step,he]

theorem stop_row (zero one : List Bool) :
    (program zero one)[stop zero one]? = some (branch (base zero one).length) := by
  have hs := stop_bound zero one
  have hrow := Shared.Codes.FiniteProgramTaggedLoop.stop_row zero one
  unfold program
  rw [List.getElem?_append_left (by simp [loop_length]; omega),List.getElem?_set_ne (by omega)]
  exact hrow

theorem bridge_row (zero one : List Bool) :
    (program zero one)[(base zero one).length]? = some (bridge ((base zero one).length+1)) := by
  simp [program,List.getElem?_append_left,loop_length]

theorem terminal_row (zero one : List Bool) :
    (program zero one)[(program zero one).length-1]? = some dummy := by
  simp [program,loop_length]

theorem terminal_step (zero one : List Bool) (t : Tape) :
    step (program zero one) ((program zero one).length-1,t) = some (.inl false) := by
  have h := terminal_row zero one
  cases ht : t.2.1 <;> simp [step,h,dummy,ht]

theorem finish (zero one : List Bool) (b : Bool) (L R : List Bool) :
    run (program zero one) (stop zero one,tapeAt L (b::false::R)) 2 =
      some (.inr ((program zero one).length-1,tapeAt L (b::false::R))) := by
  have hs := stop_row zero one
  have hb := bridge_row zero one
  cases b <;> simp only [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,length,
    Bool.false_eq_true,reduceIte,Bool.not_false,Bool.not_true,
    List.head?_cons,List.tail_cons,Option.getD_some]
    <;> simp

/-- One selected-word cycle ends at the final row ready for a splice. -/
theorem cycle (zero one : List Bool) (b prior p : Bool) (xs L : List Bool) :
    run (program zero one) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
      (cost zero one b xs) =
      some (.inr ((program zero one).length-1,
        tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false]))) := by
  have hfirst := Shared.Codes.FiniteProgramExtendAdvance.extend_advance zero one [] b prior p xs L
  dsimp only at hfirst
  change run (base zero one) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
    (16*xs.length+16*(if b then one else zero).length+29) =
      some (.inr (stop zero one,tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false]))) at hfirst
  have hp := Shared.Codes.FiniteProgramFirstEntry.first_entry (base zero one) (program zero one)
    _ _ _ (stop zero one) false (base_valid zero one) (by simp [base_length])
    (base_stop zero one) (base_other zero one) hfirst
  have ht : cost zero one b xs = (16*xs.length+16*(if b then one else zero).length+29)+2 := by simp [cost]
  rw [ht,run_continue _ _ _ _ _ hp]
  simp only [List.cons_append]
  exact finish zero one p L (tagged (output zero one b xs) ++ [false,false])

theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  let p := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  let m := p.length+1
  have hm : (program zero one).length = m := by simp [program,m,p]
  have hold : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one
    change valid p = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hbound : p.length ≤ m := by simp [m]
  have hp : ∀ r ∈ p.set (base zero one).length (bridge ((base zero one).length+1)),
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with ho | he
    · obtain ⟨h₁,h₂⟩ := hold r ho
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₁,
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₂⟩
    · subst r
      have hb : (base zero one).length+1 < m := by simp [m,p,loop_length]
      simp [bridge,validRow,hb]
  have hd : validRow m dummy.1 = true ∧ validRow m dummy.2 = true := by simp [dummy,validRow]
  have hall : (program zero one).all
      (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ p.set (base zero one).length (bridge ((base zero one).length+1)) ∨ r = dummy := by
      simpa [program,p,List.mem_append] using hr
    rw [hm]
    rcases hr' with hp' | hd'
    · simpa only [Bool.and_eq_true] using hp r hp'
    · subst r; simpa only [Bool.and_eq_true] using hd
  have hn : (program zero one).isEmpty = false := by simp [program]
  change (!(program zero one).isEmpty && (program zero one).all
    (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2)) = true
  rw [hn,hall]
  rfl

end Shared.Codes.FiniteProgramPhase

import Shared.Codes.FiniteProgramFirstEntry
import Shared.Codes.FiniteProgramTaggedExtend
import Shared.Codes.FiniteProgramTaggedAdvance

/-! Link a tagged-buffer extension to the next-source advance with a charged
handoff. The concrete table reuses both previously verified passes. -/
namespace Shared.Codes.FiniteProgramExtendAdvance
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift link_row)
open Shared.Codes.FiniteProgramTaggedExtend (stage stagePre stagePre_length stage_run stage_valid recovery)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.CircuitTable (step_eq_executeRow)

def old (zero one : List Bool) : Program := stage zero one []
def stop (zero one : List Bool) : Nat := (stagePre zero one).length+7

def shiftProgram : Program := Shared.Codes.FiniteProgramTaggedAdvance.program
  [((false,true,0,1),(true,true,0,1))]

theorem shiftProgram_valid : valid shiftProgram = true := by decide

def branch (target : Nat) : Row × Row :=
  ((false,true,target,0),(true,true,target,0))

def bridge (target : Nat) : Row × Row :=
  ((false,false,target,0),(true,false,target,0))

def handoffPre (zero one : List Bool) : Program :=
  let p := old zero one
  p.set (stop zero one) (branch p.length) ++ [bridge (p.length+1)]

def program (zero one : List Bool) (suffix : Program) : Program :=
  link (handoffPre zero one) shiftProgram suffix

theorem old_length (zero one : List Bool) : (old zero one).length = (stagePre zero one).length+8 := by
  simp [old,stage,link,recovery]

theorem stop_bound (zero one : List Bool) : stop zero one < (old zero one).length := by
  simp [stop,old_length]

theorem prefix_length (zero one : List Bool) : (handoffPre zero one).length = (old zero one).length+1 := by
  simp [handoffPre]

theorem old_valid (zero one : List Bool) : valid (old zero one) = true := by
  apply stage_valid zero one []
  simp

theorem old_stop (zero one : List Bool) (t : Tape) :
    step (old zero one) (stop zero one,t) = some (.inl false) := by
  have hrow := link_row (stagePre zero one) recovery [] 7
    (((false,true,0,1),(true,true,0,1)) : Row × Row) (by decide)
  have hr : rowAt (old zero one) (stop zero one,t) =
      some (if t.2.1 then (shiftPair (stagePre zero one).length ((false,true,0,1),(true,true,0,1))).2
        else (shiftPair (stagePre zero one).length ((false,true,0,1),(true,true,0,1))).1) := by
    simp [rowAt,old,stage,stop,hrow]
  rw [step_eq_executeRow _ _ _ hr]
  cases h : t.2.1 <;> simp [shiftPair,Shared.Codes.FiniteProgramLink.shiftRow,executeRow]

theorem old_other (zero one : List Bool) (suffix : Program) (d : Config)
    (hd : d.1 < (old zero one).length) (hne : d.1 ≠ stop zero one) :
    step (old zero one) d = step (program zero one suffix) d := by
  have hlookup : (program zero one suffix)[d.1]? = (old zero one)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hlookup]

theorem new_stop_row (zero one : List Bool) (suffix : Program) :
    (program zero one suffix)[stop zero one]? = some (branch (old zero one).length) := by
  have hs := stop_bound zero one
  simp [program,link,handoffPre,List.getElem?_append_left,hs]

theorem bridge_row (zero one : List Bool) (suffix : Program) :
    (program zero one suffix)[(old zero one).length]? = some (bridge ((old zero one).length+1)) := by
  simp [program,link,handoffPre]

/-- First preserve the old run up to its return state, then execute two
charged moves which restore the same tape at the relocated advance entry. -/
theorem handoff (zero one : List Bool) (suffix : Program) (b : Bool) (L R : List Bool) :
    run (program zero one suffix) (stop zero one,tapeAt L (b::false::R)) 2 =
      some (.inr (shiftConfig (handoffPre zero one).length (0,tapeAt L (b::false::R)))) := by
  have hs := new_stop_row zero one suffix
  have hb := bridge_row zero one suffix
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,shiftConfig,prefix_length]

/-- One selected-word extension followed by a charged handoff and one
source advance. The predecessor bit must be present immediately to the left. -/
theorem extend_advance (zero one : List Bool) (suffix : Program) (b prior p : Bool) (xs L : List Bool) :
    let word := if b then one else zero
    let buffer := xs ++ b::word
    run (program zero one suffix) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
      (16*xs.length+16*word.length+29) =
      some (.inr ((handoffPre zero one).length+14,
        tapeAt L (p::false::tagged buffer ++ [false,false]))) := by
  dsimp only
  let word := if b then one else zero
  let buffer := xs ++ b::word
  have hfirst := stage_run zero one [] b prior xs (p::L)
  dsimp only at hfirst
  change run (old zero one) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
    (6*xs.length+6*word.length+12) =
      some (.inr (stop zero one,tapeAt (p::L) (b::false::tagged buffer ++ [false]))) at hfirst
  have hpreserved := Shared.Codes.FiniteProgramFirstEntry.first_entry
    (old zero one) (program zero one suffix) _ _ _ (stop zero one) false
    (old_valid zero one) (by simp [old_length]) (old_stop zero one)
    (old_other zero one suffix) hfirst
  have hlength : buffer.length = xs.length+1+word.length := by simp [buffer]; omega
  have htime : 16*xs.length+16*word.length+29 =
      (6*xs.length+6*word.length+12)+(2+(10*buffer.length+5)) := by rw [hlength]; omega
  rw [htime,run_continue _ _ _ _ _ hpreserved]
  have hh := handoff zero one suffix b (p::L) (tagged buffer ++ [false])
  simp only [List.cons_append]
  rw [run_continue _ _ _ 2 _ hh]
  have hs := run_shift (handoffPre zero one) shiftProgram suffix shiftProgram_valid
    (0,tapeAt (p::L) (b::false::tagged buffer ++ [false]))
    (by simp [shiftProgram,Shared.Codes.FiniteProgramTaggedAdvance.program]) (10*buffer.length+5)
  have ha := Shared.Codes.FiniteProgramTaggedAdvance.advance
    [((false,true,0,1),(true,true,0,1))] b p buffer L []
  change run shiftProgram (0,tapeAt (p::L) (b::false::tagged buffer ++ [false]))
      (10*buffer.length+5) = some (.inr (14,tapeAt L (p::false::tagged buffer ++ [false,false]))) at ha
  rw [ha] at hs
  simpa [program,shiftProgram,shiftStatus,shiftConfig,buffer,word,List.cons_append] using hs

/-- Every generated row is valid if the caller's appended suffix is valid at
the total table size. The handoff and relocated advance add no assumptions. -/
theorem program_valid (zero one : List Bool) (suffix : Program)
    (hsuffix : ∀ r ∈ suffix,
      validRow ((handoffPre zero one).length+shiftProgram.length+suffix.length) r.1 = true ∧
      validRow ((handoffPre zero one).length+shiftProgram.length+suffix.length) r.2 = true) :
    valid (program zero one suffix) = true := by
  let pre := handoffPre zero one
  let m := pre.length+shiftProgram.length+suffix.length
  have hm : (program zero one suffix).length = m := by simp [program,link,m,pre]; omega
  have hold : ∀ r ∈ old zero one, validRow (old zero one).length r.1 = true ∧
      validRow (old zero one).length r.2 = true := by
    intro r hr
    have hv := old_valid zero one
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hshift : ∀ r ∈ shiftProgram, validRow shiftProgram.length r.1 = true ∧
      validRow shiftProgram.length r.2 = true := by
    intro r hr
    have hv := shiftProgram_valid
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hlen : (old zero one).length+1 < m := by
    simp [m,pre,prefix_length,shiftProgram,Shared.Codes.FiniteProgramTaggedAdvance.program]
    omega
  have hmono : (old zero one).length ≤ m := by omega
  have hpre : ∀ r ∈ pre, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hr' : r ∈ (old zero one).set (stop zero one) (branch (old zero one).length) ∨
        r = bridge ((old zero one).length+1) := by
      simpa [pre,handoffPre,List.mem_append] using hr
    rcases hr' with hp | hb
    · rcases List.mem_or_eq_of_mem_set hp with ho | he
      · obtain ⟨h₁,h₂⟩ := hold r ho
        exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hmono h₁,
          Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hmono h₂⟩
      · subst r
        have hbnd : (old zero one).length < m := by omega
        simp [branch,validRow,hbnd]
    · subst r
      simp [bridge,validRow,hlen]
  have hall : (program zero one suffix).all
      (fun r => validRow (program zero one suffix).length r.1 &&
        validRow (program zero one suffix).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre ∨ r ∈ shiftProgram.map (shiftPair pre.length) ∨ r ∈ suffix := by
      simpa [program,link,pre,List.mem_append] using hr
    rw [hm]
    rcases hr' with hp | hs | ht
    · simpa only [Bool.and_eq_true] using hpre r hp
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hs
      obtain ⟨h₁,h₂⟩ := hshift r' hr'
      have hbound : pre.length+shiftProgram.length ≤ m := by simp [m]
      have h₁' := Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 pre.length _ h₁
      have h₂' := Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 pre.length _ h₂
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₁',
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₂'⟩
    · simpa only [Bool.and_eq_true,m,pre] using hsuffix r ht
  have hn : (program zero one suffix).isEmpty = false := by
    cases h : program zero one suffix with
    | nil =>
      simp [h] at hm
      simp [m,pre,prefix_length,shiftProgram,Shared.Codes.FiniteProgramTaggedAdvance.program] at hm
      omega
    | cons r rs => rfl
  change (!(program zero one suffix).isEmpty && (program zero one suffix).all
    (fun r => validRow (program zero one suffix).length r.1 &&
      validRow (program zero one suffix).length r.2)) = true
  rw [hn,hall]
  rfl

namespace Fixtures
example : run (program [false] [true] []) (0,tapeAt [true] [false,false,false,false,false]) 45 =
    some (.inr (44,tapeAt [] (true::false::tagged [false,false] ++ [false,false]))) := by decide
example : run (program [false] [true] []) (0,tapeAt [false] [true,false,false,false,false]) 45 =
    some (.inr (44,tapeAt [] (false::false::tagged [true,true] ++ [false,false]))) := by decide
end Fixtures

end Shared.Codes.FiniteProgramExtendAdvance

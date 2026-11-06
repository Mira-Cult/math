import Shared.Codes.FiniteProgramScanHead

/-! A fixed finite table links the frame-removal loop to the reflected
untagger at the first empty-frame entry. Both handoff moves are charged. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Codes.FiniteProgramFrameUntag

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (framed words totalCost padding empty)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base (width : Nat) := Shared.Codes.FiniteProgramFrameLoop.program width

def pre (width : Nat) : Program :=
  (base width).set (empty width) (branch (base width).length) ++ [bridge ((base width).length+1)]

def program (width : Nat) : Program := link (pre width) Shared.Codes.FiniteProgramMirror.positioned []

@[simp] theorem pre_length (width : Nat) : (pre width).length = (base width).length+1 := by simp [pre]

/-- This is the size of this auxiliary finite program, not a beeper record. -/
theorem program_length (width : Nat) : (program width).length = 8*width+101 := by
  simp [program,link,pre_length,base,Shared.Codes.FiniteProgramFrameLoop.length,
    Shared.Codes.FiniteProgramMirror.positioned_length]

theorem empty_bound (width : Nat) : empty width < (base width).length := by
  simp [empty,base,Shared.Codes.FiniteProgramFrameLoop.length]

theorem base_other (width : Nat) (d : Config) (hd : d.1 < (base width).length)
    (hne : d.1 ≠ empty width) : step (base width) d = step (program width) d := by
  have he : (program width)[d.1]? = (base width)[d.1]? := by
    simp [program,link,pre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,he]

theorem stop_row (width : Nat) :
    (program width)[empty width]? = some (branch (base width).length) := by
  simp [program,link,pre,List.getElem?_append_left,empty_bound]

theorem bridge_row (width : Nat) :
    (program width)[(base width).length]? = some (bridge ((base width).length+1)) := by
  simp [program,link,pre]

/-- Two real moves preserve the boundary and enter the untagger. -/
theorem handoff (width : Nat) (b : Bool) (L R : List Bool) :
    run (program width) (empty width,tapeAt L (b::false::R)) 2 =
      some (.inr ((pre width).length,tapeAt L (b::false::R))) := by
  have hs := stop_row width
  have hb := bridge_row width
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,pre_length]

theorem program_valid (width : Nat) : valid (program width) = true := by
  let s := base width
  let d := Shared.Codes.FiniteProgramMirror.positioned
  let k := s.length+1
  let m := k+d.length
  have hl : (program width).length = m := by simp [program,link,pre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramFrameLoop.program_valid width
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
  have hall : (program width).all
      (fun r => validRow (program width).length r.1 && validRow (program width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ s.set (empty width) (branch s.length) ∨ r = bridge k ∨
        r ∈ d.map (shiftPair k) := by
      simpa [program,link,pre,pre_length,s,d,k,List.mem_append] using hr
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
  have hn : (program width).isEmpty = false := by
    cases h : program width with
    | nil => simp [h] at hl; dsimp [m,k] at hl; omega
    | cons r rs => rfl
  change (!(program width).isEmpty && (program width).all
    (fun r => validRow (program width).length r.1 && validRow (program width).length r.2)) = true
  rw [hn,hall]
  rfl

/-- Frame removal and untagging are one finite-table run; the original
source boundary is two zeros and both handoff transitions are counted. -/
theorem frame_then_untag (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width)
    (kept L R : List Bool) (hk : kept.length = width) :
    let out := kept++words items
    run (program width) (0,tapeAt (false::L) (false::false::tagged (kept++framed items) ++ false::R))
      (totalCost width items+2+(2+Shared.Codes.FiniteProgramUntag.cost out.reverse)) =
      some (.inr ((pre width).length+14,tapeAt
        (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L))
        (out++false::padding items.length R))) := by
  dsimp only
  let out := kept++words items
  let source := tapeAt (cursor false (false::L) out).2
    ((cursor false (false::L) out).1::false::false::padding items.length R)
  let target := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L))
    (out++false::padding items.length R)
  have hframe := Shared.Codes.FiniteProgramFrameLoop.run_frames width items hwidth kept (false::L) R false hk
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (base width) (program width)
    _ _ (totalCost width items) (empty width) false
    (Shared.Codes.FiniteProgramFrameLoop.program_valid width) (by simp [base,Shared.Codes.FiniteProgramFrameLoop.length])
    (Shared.Codes.FiniteProgramScanRaw.loop_empty width) (base_other width) hframe
  have htwo := handoff width (cursor false (false::L) out).1
    (cursor false (false::L) out).2 (false::padding items.length R)
  change run (program width) (empty width,source) 2 = _ at htwo
  have hraw := Shared.Codes.FiniteProgramMirror.positioned_run out L (padding items.length R)
  change run Shared.Codes.FiniteProgramMirror.positioned (0,source)
    (2+Shared.Codes.FiniteProgramUntag.cost out.reverse) = some (.inr (14,target)) at hraw
  have hshift := run_shift (pre width) Shared.Codes.FiniteProgramMirror.positioned []
    Shared.Codes.FiniteProgramMirror.positioned_valid (0,source)
    (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
    (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)
  rw [hraw] at hshift
  change run (program width) (shiftConfig (pre width).length (0,source)) _ = _ at hshift
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ htwo]
  simpa only [shiftConfig,shiftStatus,Nat.add_zero] using hshift

/-- The frame pass, two handoff moves and untagger have a joint explicit
quadratic bound in the number of frames and output bits. -/
theorem frame_untag_cost_bound (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width) (kept : List Bool) :
    let out := kept++words items
    totalCost width items+2+(2+Shared.Codes.FiniteProgramUntag.cost out.reverse) ≤
      (items.length+1)*(7*width+30*((items.length+1)*(width+1))+26)+2+
        (out.length*(20*out.length+21)+6) := by
  have hf := Shared.Codes.FiniteProgramFrameLoop.totalCost_bound width items hwidth
  have hu := Shared.Codes.FiniteProgramMirror.positioned_cost_bound (kept++words items)
  omega

end Shared.Codes.FiniteProgramFrameUntag

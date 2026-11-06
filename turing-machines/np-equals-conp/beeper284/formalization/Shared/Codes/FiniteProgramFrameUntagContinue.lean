import Shared.Codes.FiniteProgramFrameUntag
import Shared.Codes.FiniteProgramTwoExit

/-! Attach a valid finite continuation to the first untagging exit. The
link consists of actual finite rows and two physical moves, not a free jump. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Codes.FiniteProgramFrameUntagContinue

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramFrameUntag (pre)
open Shared.Codes.FiniteProgramLink (link_row shiftPair shiftRow shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTwoExit (handoff_second)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def stop (width : Nat) : Nat := (pre width).length+14

def program (width : Nat) (next : Program) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program (Shared.Codes.FiniteProgramFrameUntag.program width) next
    (stop width) (stop width)

theorem stop_bound (width : Nat) : stop width < (Shared.Codes.FiniteProgramFrameUntag.program width).length := by
  simp [stop,Shared.Codes.FiniteProgramFrameUntag.program,
    Shared.Codes.FiniteProgramLink.link,Shared.Codes.FiniteProgramMirror.positioned_length]

theorem stop_step (width : Nat) (t : Tape) :
    step (Shared.Codes.FiniteProgramFrameUntag.program width) (stop width,t) = some (.inl false) := by
  have hr := link_row (pre width) Shared.Codes.FiniteProgramMirror.positioned [] 14
    (((false,false,2,1),(true,false,2,1)) : Row × Row) (by decide)
  change (Shared.Codes.FiniteProgramFrameUntag.program width)[stop width]? = _ at hr
  cases h : t.2.1 <;> simp [step,hr,shiftPair,shiftRow,h]

theorem program_valid (width : Nat) (next : Program) (hn : valid next = true) :
    valid (program width next) = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid _ _ _ _
    (Shared.Codes.FiniteProgramFrameUntag.program_valid width) hn (stop_bound width) (stop_bound width)

theorem program_length (width : Nat) (next : Program) :
    (program width next).length = 8*width+103+next.length := by
  simp [program,Shared.Codes.FiniteProgramTwoExit.program_length,
    Shared.Codes.FiniteProgramFrameUntag.program_length]

/-- The appended continuation has its own fixed offset; its entire bounded
execution is charged step-for-step. -/
theorem continuation_run (width : Nat) (next : Program) (hn : valid next = true)
    (c : Config) (hc : c.1 < next.length) (fuel : Nat) :
    run (program width next)
      (shiftConfig ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2) c) fuel =
      shiftStatus ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2) (run next c fuel) := by
  simpa [program,Shared.Codes.FiniteProgramTwoExit.program,Shared.Codes.FiniteProgramTwoExit.pre_length] using
    run_shift (Shared.Codes.FiniteProgramTwoExit.pre
      (Shared.Codes.FiniteProgramFrameUntag.program width) (stop width) (stop width)) next [] hn c hc fuel

/-- Two moves preserve the first two output cells and enter the appended
continuation. The arbitrary high output suffix and opposite tape are kept. -/
theorem handoff (width : Nat) (next : Program) (head second : Bool) (L R : List Bool) :
    run (program width next) (stop width,tapeAt L (head::second::R)) 2 =
      some (.inr (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2),
        tapeAt L (head::second::R))) := by
  simpa [program,Shared.Codes.FiniteProgramTwoExit.pre_length] using
    handoff_second (Shared.Codes.FiniteProgramFrameUntag.program width) next
      (stop width) (stop width) (stop_bound width) head second L R

/-- Every live run ending at the first untagging exit is unchanged by the
splice, including all earlier frame and untagging steps. -/
theorem preserve_to_stop (width : Nat) (next : Program) (c last : Config) (n : Nat)
    (hc : c.1 < (Shared.Codes.FiniteProgramFrameUntag.program width).length)
    (h : run (Shared.Codes.FiniteProgramFrameUntag.program width) c n = some (.inr last)) :
    run (program width next) c n = some (.inr last) := by
  exact Shared.Codes.FiniteProgramTwoExit.first_entry _ _ (stop width) (stop width) c last n
    (Shared.Codes.FiniteProgramFrameUntag.program_valid width) hc (stop_step width) (stop_step width) h


theorem padding_length (n : Nat) (tail : List Bool) :
    (Shared.Codes.FiniteProgramFrameLoop.padding n tail).length = 3*n+tail.length := by
  induction n generalizing tail with
  | zero => simp [Shared.Codes.FiniteProgramFrameLoop.padding]
  | succ n ih =>
    simp only [Shared.Codes.FiniteProgramFrameLoop.padding,ih,List.length_cons]
    omega

/-- The constructed output always has two explicit cells available at its
head, including when the raw output word is empty. -/
theorem output_handoff (width : Nat) (next : Program) (words L : List Bool) (frames : Nat) :
    let right := words++false::Shared.Codes.FiniteProgramFrameLoop.padding frames [false,false]
    run (program width next) (stop width,tapeAt L right) 2 =
      some (.inr (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2),tapeAt L right)) := by
  dsimp only
  let right := words++false::Shared.Codes.FiniteProgramFrameLoop.padding frames [false,false]
  have hlen : 2 ≤ right.length := by
    simp [right,padding_length]
    omega
  change run (program width next) (stop width,tapeAt L right) 2 =
    some (.inr (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2),tapeAt L right))
  cases h : right with
  | nil => simp [h] at hlen
  | cons head rest =>
    cases ht : rest with
    | nil => simp [h,ht] at hlen
    | cons second tail =>
      exact handoff width next head second L tail

/-- Frame removal, untagging, the two paid splice moves, and the supplied
continuation run all occur in one valid finite program. -/
theorem frame_untag_then (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width)
    (kept L : List Bool) (hk : kept.length = width)
    (next : Program) (hn : valid next = true) (fuel : Nat) (last : Config)
    (hnext : run next (0,tapeAt
      (false::false::Shared.Codes.FiniteProgramUntag.padding
        (kept++Shared.Codes.FiniteProgramFrameLoop.words items).length (false::L))
      ((kept++Shared.Codes.FiniteProgramFrameLoop.words items)++false::
        Shared.Codes.FiniteProgramFrameLoop.padding items.length [false,false])) fuel = some (.inr last)) :
    let out := kept++Shared.Codes.FiniteProgramFrameLoop.words items
    let clock := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
      (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)
    run (program width next)
      (0,tapeAt (false::L) (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
        (kept++Shared.Codes.FiniteProgramFrameLoop.framed items) ++ false::[false,false]))
      (clock+2+fuel) =
        some (.inr (shiftConfig ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2) last)) := by
  dsimp only
  let out := kept++Shared.Codes.FiniteProgramFrameLoop.words items
  let clock := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
    (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)
  let left := false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L)
  let right := out++false::Shared.Codes.FiniteProgramFrameLoop.padding items.length [false,false]
  let init := (0,tapeAt (false::L) (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
    (kept++Shared.Codes.FiniteProgramFrameLoop.framed items) ++ false::[false,false]))
  have hb := Shared.Codes.FiniteProgramFrameUntag.frame_then_untag width items hwidth kept L [false,false] hk
  change run (Shared.Codes.FiniteProgramFrameUntag.program width) init clock =
    some (.inr (stop width,tapeAt left right)) at hb
  have hp := preserve_to_stop width next init (stop width,tapeAt left right) clock
    (by simp [init,Shared.Codes.FiniteProgramFrameUntag.program_length]) hb
  have hh := output_handoff width next out left items.length
  change run (program width next) (stop width,tapeAt left right) 2 = _ at hh
  have hn0 : 0 < next.length := Shared.Codes.FiniteProgramLink.valid_nonempty next hn
  have hcontinue := continuation_run width next hn (0,tapeAt left right) hn0 fuel
  change run (program width next)
    (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2),tapeAt left right) fuel = _ at hcontinue
  change run next (0,tapeAt left right) fuel = some (.inr last) at hnext
  rw [hnext] at hcontinue
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hp,run_continue _ _ _ _ _ hh]
  exact hcontinue


namespace Fixtures

def loop : Program := [((false,true,0,0),(true,true,0,0))]

example : (program 0 loop).length = 104 := by simp [program_length,loop]
example : valid (program 0 loop) = true := program_valid 0 loop (by decide +kernel)

end Fixtures

end Shared.Codes.FiniteProgramFrameUntagContinue

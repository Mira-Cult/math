import Shared.Codes.FiniteProgramMirror
import Shared.Codes.FiniteProgramOneExit
import Shared.Codes.FiniteProgramScanHead
import Shared.ComplexityBridge.TM2OutputProtectedCompact

/-! Scan right across a tagged buffer, then use the reflected untagger to
produce and position its raw bits modulo blank padding. This does not retain
the word length: a trailing false bit is indistinguishable from blank tape.
This finite cleanup component has a terminal placeholder and is not a total
nonhalting machine. -/
namespace Shared.Codes.FiniteProgramTaggedRawOutput
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def stop : Row × Row := ((false,true,0,1),(true,true,0,1))
def scanner : Program :=
  [ ((false,true,1,0),(true,true,1,0)),
    ((false,true,2,0),(true,true,2,0)),
    ((false,false,5,0),(true,true,3,0)),
    ((false,true,4,0),(true,true,4,0)),
    ((false,true,0,1),(true,true,2,0)),
    stop ]

theorem scanner_valid : valid scanner = true := by decide
theorem scanner_stop (t : Tape) : step scanner (5,t) = some (.inl false) := by
  cases h : t.2.1 <;> simp [scanner,stop,step,h]

def program : Program := Shared.Codes.FiniteProgramOneExit.program scanner
  Shared.Codes.FiniteProgramMirror.positioned 5

theorem program_valid : valid program = true :=
  Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ scanner_valid
    Shared.Codes.FiniteProgramMirror.positioned_valid (by simp [scanner])

@[simp] theorem program_length : program.length = 53 := by
  simp [program,Shared.Codes.FiniteProgramOneExit.offset,scanner,
    Shared.Codes.FiniteProgramMirror.positioned_length]

/-- The raw-output continuation remains a terminal placeholder, to be
replaced by a live continuation in the total machine. -/
theorem terminal_placeholder (t : Tape) : step program (22,t) = some (.inl false) := by
  have hr : program[22]? = some (((false,false,10,1),(true,false,10,1)) : Row × Row) := by decide
  have hrow : rowAt program (22,t) = some (if t.2.1 then (true,false,10,1) else (false,false,10,1)) := by
    change (program[22]?).map _ = _
    rw [hr]
    rfl
  rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow _ _ _ hrow]
  cases t.2.1 <;> rfl

theorem start (xs L R : List Bool) :
    run scanner (0,tapeAt L (false::false::tagged xs ++ false::false::R)) 2 =
      some (.inr (2,tapeAt (false::false::L) (tagged xs ++ false::false::R))) := by
  simp [scanner,run,advance,step,tapeAt,moveTape]

theorem scan_block (b : Bool) (L R : List Bool) :
    run scanner (2,tapeAt L (true::b::true::R)) 3 =
      some (.inr (2,tapeAt (true::b::true::L) R)) := by
  cases b <;> simp [scanner,run,advance,step,tapeAt,moveTape]

theorem scan_blocks (xs L R : List Bool) :
    run scanner (2,tapeAt L (tagged xs ++ false::R)) (3*xs.length) =
      some (.inr (2,tapeAt ((tagged xs).reverse ++ L) (false::R))) := by
  induction xs generalizing L with
  | nil => simp [tagged]
  | cons b xs ih =>
    simp only [tagged_cons,List.cons_append,List.length_cons]
    rw [show 3*(xs.length+1) = 3+3*xs.length by omega,
      run_continue _ _ _ 3 _ (scan_block b L _)]
    simpa [tagged_cons,List.reverse_cons,List.append_assoc] using ih (true::b::true::L)

theorem finish_scan (head : Bool) (L R : List Bool) :
    run scanner (2,tapeAt (head::L) (false::false::R)) 1 =
      some (.inr (5,tapeAt L (head::false::false::R))) := by
  cases head <;> simp [scanner,run,advance,step,tapeAt,moveTape]

/-- The scan reaches the final tag, or the separator for an empty word.
The complete tagged buffer and both boundary blanks remain on the tape. -/
theorem scan (xs L R : List Bool) :
    let c := Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) xs
    run scanner (0,tapeAt L (false::false::tagged xs ++ false::false::R)) (3*xs.length+3) =
      some (.inr (5,tapeAt c.2 (c.1::false::false::R))) := by
  dsimp only
  let c := Shared.Codes.FiniteProgramCrossTag.cursor false (false::L) xs
  have hc := Shared.Codes.FiniteProgramCrossTag.cursor_contents false (false::L) xs
  change c.1::c.2 = (tagged xs).reverse ++ false::false::L at hc
  have hs := scan_blocks xs (false::false::L) (false::R)
  rw [← hc] at hs
  rw [show 3*xs.length+3 = 2+(3*xs.length+1) by omega,
    run_continue _ _ _ 2 _ (start xs L R),run_continue _ _ _ _ _ hs]
  exact finish_scan c.1 c.2 R

def cost (xs : List Bool) : Nat :=
  (3*xs.length+3)+2+(2+Shared.Codes.FiniteProgramUntag.cost xs.reverse)

theorem cost_bound (xs : List Bool) :
    cost xs ≤ 3*xs.length+5+(xs.length*(20*xs.length+21)+6) := by
  have h := Shared.Codes.FiniteProgramMirror.positioned_cost_bound xs
  dsimp [cost]
  omega

/-- Raw binary tapes cannot distinguish an appended false bit. Any consumer
requiring the exact list length needs a separate length or framing convention. -/
theorem trailing_false_collision (xs : List Bool) :
    TapeRel (initial xs).2 (initial (xs++[false])).2 := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    simpa [initial,tapeAt] using Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank [] bs b

/-- For any blank-equivalent canonical tagged buffer, the 53-state table
returns the raw tape modulo blanks, with the head on its first bit (or blank
if empty). This alone does not recover an exact binary-list length. -/
theorem run_output (xs : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical [] false xs).2) :
    ∃ d, run program c (cost xs) = some (.inr (22,d)) ∧
      TapeRel d (initial xs).2 := by
  let R : List Bool := [false,false,false,false,false]
  let startTape := tapeAt [] (false::false::tagged xs ++ false::false::R)
  let cur := Shared.Codes.FiniteProgramCrossTag.cursor false [false] xs
  let mid := tapeAt cur.2 (cur.1::false::false::R)
  let result := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding xs.length [false])
    (xs ++ false::R)
  have hpad : TapeRel (canonical [] false xs).2 startTape := by
    have h := Shared.ComplexityBridge.TM2OutputFirstCell.append_blanks []
      (false::tagged xs ++ [false,false,false]) false 4
    simpa [canonical,startTape,R,List.append_assoc,TapeRel] using h
  have hscan := scan xs [] R
  change run scanner (0,startTape) (3*xs.length+3) = some (.inr (5,mid)) at hscan
  have hfirst := Shared.Codes.FiniteProgramOneExit.first_entry scanner
    Shared.Codes.FiniteProgramMirror.positioned 5 (0,startTape) (5,mid) (3*xs.length+3)
    scanner_valid (by simp [scanner]) scanner_stop hscan
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff scanner
    Shared.Codes.FiniteProgramMirror.positioned 5 (by simp [scanner]) mid
  have hmirror := Shared.Codes.FiniteProgramMirror.positioned_run xs [] R
  change run Shared.Codes.FiniteProgramMirror.positioned (0,mid)
    (2+Shared.Codes.FiniteProgramUntag.cost xs.reverse) = some (.inr (14,result)) at hmirror
  let bounced := Shared.Codes.FiniteProgramThreeExit.bounce mid
  have hrel := run_related Shared.Codes.FiniteProgramMirror.positioned (0,bounced) (0,mid) rfl
    (Shared.Codes.FiniteProgramThreeExit.bounce_related mid)
    (2+Shared.Codes.FiniteProgramUntag.cost xs.reverse)
  rw [hmirror] at hrel
  cases hr : run Shared.Codes.FiniteProgramMirror.positioned (0,bounced)
      (2+Shared.Codes.FiniteProgramUntag.cost xs.reverse) with
  | none => rw [hr] at hrel; exact False.elim hrel
  | some value => cases value with
    | inl out => rw [hr] at hrel; exact False.elim hrel
    | inr d =>
      have hd : d.1 = 14 ∧ TapeRel d.2 result := by simpa only [hr,StatusRel] using hrel
      have hshift := Shared.Codes.FiniteProgramOneExit.continuation scanner
        Shared.Codes.FiniteProgramMirror.positioned 5 Shared.Codes.FiniteProgramMirror.positioned_valid
        (0,bounced) (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
        (2+Shared.Codes.FiniteProgramUntag.cost xs.reverse)
      rw [hr] at hshift
      have hcanonical : run program (0,startTape) (cost xs) = some (.inr (8+d.1,d.2)) := by
        change run (Shared.Codes.FiniteProgramOneExit.program scanner
          Shared.Codes.FiniteProgramMirror.positioned 5) _ _ = _
        rw [show cost xs = (3*xs.length+3)+(2+(2+Shared.Codes.FiniteProgramUntag.cost xs.reverse)) by dsimp [cost]; omega,
          run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hhand]
        simpa [scanner,Shared.Codes.FiniteProgramOneExit.offset,bounced,shiftConfig,shiftStatus] using hshift
      have hrun := run_related program c (0,startTape) (by simpa using hq) (ht.trans hpad) (cost xs)
      rw [hcanonical] at hrun
      cases hc : run program c (cost xs) with
      | none => rw [hc] at hrun; exact False.elim hrun
      | some val => cases val with
        | inl out => rw [hc] at hrun; exact False.elim hrun
        | inr final =>
          have hf : final.1 = 8+d.1 ∧ TapeRel final.2 d.2 := by simpa only [hc,StatusRel] using hrun
          refine ⟨final.2,?_,?_⟩
          · simp only [Option.some.injEq,Sum.inr.injEq]
            exact Prod.ext (by simpa [hd.1] using hf.1) rfl
          · have hout : TapeRel result (initial xs).2 := by
              simpa [result,R,Shared.Codes.FiniteProgramFrameLoop.padding] using
                Shared.Codes.FiniteProgramScanHead.result_tape_initial xs 0
            exact (hf.2.trans hd.2).trans hout

end Shared.Codes.FiniteProgramTaggedRawOutput

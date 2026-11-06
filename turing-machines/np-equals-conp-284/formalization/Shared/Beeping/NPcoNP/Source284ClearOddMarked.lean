import Shared.Beeping.NPcoNP.Source284ScratchCompactMarked

/-! Clear a one sentinel and transfer the resulting zero across the protected
frame as a one mark, retaining the arbitrary certificate and scratch suffix. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284ClearOddMarked

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨false,true,some 2⟩
  else shiftRow 2 (Source284ScratchCompactMarked.table continuation (q-2) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (16+states) (table continuation) := by
  have hc := Source284ScratchCompactMarked.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [table,h0] at hnext; omega
    · have ht : (shiftRow 2 (Source284ScratchCompactMarked.table continuation (q-2) b)).next = some q' := by
        simpa [table,h0,h1] using hnext
      cases he : (Source284ScratchCompactMarked.table continuation (q-2) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hc (q-2) (by omega) b r he
        simp [shiftRow,he] at ht
        subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (2+q) b = shiftRow 2 (Source284ScratchCompactMarked.table continuation q b) := by
  simp [table,show 2+q ≠ 1 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284ScratchCompactMarked.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284ScratchCompactMarked.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- The sentinel is overwritten by two real steps. The existing compactor
then transfers its zero cell across the whole frame in finite time. -/
theorem clear_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨2*certificate+1,2*flipped w tail,some 0⟩
      (8*w.length+13+fuel) =
    shiftConfig 16 (run continuation ⟨certificate,2*flipped w (2*tail+1),some 0⟩ fuel) := by
  have hsteps : run (table continuation) ⟨2*certificate+1,2*flipped w tail,some 0⟩ 2 =
      shiftConfig 2 ⟨2*certificate,2*flipped w tail,some 0⟩ := by
    simp [run,step,table,shiftConfig,bit,Nat.testBit_zero] <;> omega
  have ht : 8*w.length+13+fuel = 2+(8*w.length+11+fuel) := by omega
  rw [ht,Source284ScratchFlipReturn.run_add,hsteps,relocated_run,
    Source284ScratchCompactMarked.compact_after,Source284SourceRelocation.shiftConfig_add]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨7,0,some 0⟩ 13 = ⟨3,8,some 16⟩ := by decide +kernel
example : run (table loop) ⟨7,150,some 0⟩ 29 = ⟨3,406,some 16⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284ClearOddMarked

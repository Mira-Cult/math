import Shared.Beeping.NPcoNP.Source284DualReturn
import Shared.Beeping.NPcoNP.Source284NestedMarkRestore

/-! Both outer-marker outcomes restore the same original inner block and
scratch boundary in one finite source table. The resulting branch-specific
states are sinks; binding them to a looping controller is separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284NestedBothBranches

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284NestedMarker.table (Source284DualReturn.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (43+states) (table continuation) := by
  have hr := Source284DualReturn.closed states continuation hn hv
  have hm := Source284NestedMarker.closed (26+states) (Source284DualReturn.table continuation) (by omega) hr
  have he : 17+(26+states) = 43+states := by omega
  rw [he] at hm
  exact hm

theorem mark (continuation : Nat → Bool → Row) (m k : Nat) (rest : List Bool)
    (certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*stream,some 0⟩ (4*m+4*k+14) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*stream,some 31⟩ := by
  have ht : 4*m+4*k+14 = (2*(List.replicate m false).length+4*k+8)+(2*m+6) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add]
  unfold table
  rw [Source284NestedMarker.mark_outer]
  change run (Source284NestedMarker.table (Source284DualReturn.table continuation))
    (shiftConfig 17 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      4*Source284ScratchScanner.push (2*stream+1) (List.replicate m false),some 0⟩) _ = _
  rw [Source284NestedMarkRestore.continuation_run,Source284DualReturn.restore _ 0 m _ _ (by omega)]
  rfl

theorem exhausted (continuation : Nat → Bool → Row) (m k certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
        2*stream,some 0⟩ (4*m+4*k+14) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
      2*stream,some 42⟩ := by
  have ht : 4*m+4*k+14 = (2*(List.replicate m false).length+4*k+8)+(2*m+6) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add]
  unfold table
  rw [Source284NestedMarker.outer_exhausted]
  change run (Source284NestedMarker.table (Source284DualReturn.table continuation))
    (shiftConfig 17 ⟨pairTape (List.replicate k true) certificate,
      4*Source284ScratchScanner.push (2*stream+1) (List.replicate m false),some 1⟩) _ = _
  rw [Source284NestedMarkRestore.continuation_run,Source284DualReturn.restore _ 1 m _ _ (by omega)]
  rfl

theorem source_mark (states : Nat) (continuation : Nat → Bool → Row)
    (m k : Nat) (rest : List Bool) (certificate stream : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (43+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate)))
      (4*m+4*k+14) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*stream,active 31⟩ := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*stream,some 0⟩
  have hi : Valid (43+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (43+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*m+4*k+14)
  rw [mark] at hr
  exact hr

theorem source_exhausted (states : Nat) (continuation : Nat → Bool → Row)
    (m k certificate stream : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (43+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate)))
      (4*m+4*k+14) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,active 42⟩ := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  have hi : Valid (43+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (43+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*m+4*k+14)
  rw [exhausted] at hr
  exact hr


namespace Fixtures

def loop (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
example : run (table loop) ⟨pairTape [] (pairTape [false] 3),0,some 0⟩ 14 =
    ⟨pairTape [] (pairTape [true] 3),0,some 31⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [] (pairTape [] 3),0,some 0⟩ 14 =
    ⟨pairTape [] (pairTape [] 3),0,some 42⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [false] (pairTape [true] 3),0,some 0⟩ 22 =
    ⟨pairTape [false] (pairTape [true] 3),0,some 42⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedBothBranches

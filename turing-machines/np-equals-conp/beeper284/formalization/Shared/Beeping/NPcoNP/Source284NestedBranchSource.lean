import Shared.Beeping.NPcoNP.Source284NestedBranchDispatch
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Closed numeric source encoding of the two continuation branches. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284NestedBranchSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284NestedBranchDispatch

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (43+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h30 : q=30
  · subst q; simp [table] at hnext; omega
  · by_cases h41 : q=41
    · subst q; simp [table] at hnext; omega
    · by_cases hl : q<43
      · have he : (base q b).next = some q' := by simpa [table,h30,h41,hl] using hnext
        have hr := base_closed q hl b q' he
        omega
      · have he : (shiftRow 43 (continuation (q-43) b)).next = some q' := by
          simpa [table,h30,h41,hl] using hnext
        cases hh : (continuation (q-43) b).next with
        | none => simp [shiftRow,hh] at he
        | some r =>
          have hr := hv (q-43) (by omega) b r hh
          simp [shiftRow,hh] at he
          subst q'; omega

theorem source_mark_then (states : Nat) (continuation : Nat → Bool → Row)
    (m k : Nat) (rest : List Bool) (certificate stream fuel : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (encode (43+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate)))
      (4*m+4*k+14+fuel) =
    Source284SourceRelocation.lift 43
      (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
          2*stream,active 0⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*stream,some 0⟩
  have hi : Valid (43+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (43+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*m+4*k+14+fuel)
  rw [mark_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ true::rest) certificate),2*stream,some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; omega
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

theorem source_exhausted_then (states : Nat) (continuation : Nat → Bool → Row)
    (m k certificate stream fuel : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (encode (43+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate)))
      (4*m+4*k+14+fuel) =
    Source284SourceRelocation.lift 43
      (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
          2*stream,active 1⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  have hi : Valid (43+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (43+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*m+4*k+14+fuel)
  rw [exhausted_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
    2*stream,some 1⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; omega
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures

def loop (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
example : run (table loop) ⟨pairTape [] (pairTape [false] 3),0,some 0⟩ 14 =
    ⟨pairTape [] (pairTape [true] 3),0,some 43⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [] (pairTape [] 3),0,some 0⟩ 14 =
    ⟨pairTape [] (pairTape [] 3),0,some 44⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedBranchSource

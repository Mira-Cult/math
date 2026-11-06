import Shared.Beeping.NPcoNP.Source284NestedGrowthStep

/-! Numeric encoding of one finite successful outer-token growth round. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284NestedGrowthSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284NestedGrowthStep

/-- This executable numeric table makes the marked-token growth step and then
executes every requested continuation step. -/
theorem source_growth_then (states : Nat) (continuation : Nat → Bool → Row)
    (m k n : Nat) (rest w : List Bool) (certificate higher fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (85+states) (table continuation) 1)
      (Source284Relative.initial (2*flipped w (counter n higher))
        (pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate)))
      (cost m k n w.length+fuel) =
    Source284SourceRelocation.lift 85
      (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
          2*flipped w (counter (n+m) (halves m higher)),active 0⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*flipped w (counter n higher),some 0⟩
  have hi : Valid (85+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (85+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (cost m k n w.length+fuel)
  rw [growth_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ true::rest) certificate),
    2*flipped w (counter (n+m) (halves m higher)),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨pairTape [] (pairTape [false] 3),2*flipped [] (counter 0 5),some 0⟩
    (cost 0 0 0 0) = ⟨pairTape [] (pairTape [true] 3),2*flipped [] (counter 0 5),some 85⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [false] (pairTape [false] 3),2*flipped [true] (counter 0 5),some 0⟩
    (cost 1 0 0 1) = ⟨pairTape [false] (pairTape [true] 3),2*flipped [true] (counter 1 2),some 85⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedGrowthSource

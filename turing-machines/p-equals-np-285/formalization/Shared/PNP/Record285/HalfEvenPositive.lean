import Shared.PNP.Record285.HalfEvenShift

/-! Positive-even native-half operation from root to root. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfEvenPositive
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.SymbolicDispatch (bits pathLeft pathCost)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.HalfCycle (boundary cyclesCost)
attribute [local irreducible] Record285.machine

theorem return_output (gap n : Nat) (before fields : List Nat) (retained : Nat) :
    completeRight ((n+1)::foldRuns before []) gap
      (2*(2*IncrementSelector.blocksBits fields (4*retained+1))+1) =
    4*IncrementSelector.blocksBits
      (gap::(before++[n+1]++fields++[0])) retained := by
  rw [IncrementMeaning.scan_output]
  simp only [IncrementMeaning.backFold]
  rw [IncrementMeaning.backFold_foldRuns]
  simp only [IncrementMeaning.backFold,← IncrementMeaning.blocks_cons,← IncrementMeaning.blocks_append]
  have hz : 4*retained+1 = IncrementSelector.blocksBits [0] retained := by
    simp [IncrementSelector.blocksBits,runPattern,bitVal]; omega
  rw [hz,← IncrementMeaning.blocks_append]
  congr 2
  simp [List.append_assoc]

theorem return_to_break (gap n : Nat) (before fields : List Nat) (head : Int) (far retained : Nat) :
    let pos := head+1+IncrementSelector.cost (gap::before)+2+n
    let steps := 1+completeCost ((n+1)::foldRuns before []) gap
    silent Record285.machine steps
      (atLeftWord DecrementZero.scan (pos-1)
        (1+2*pushBit n true (1+2*DecrementSelector.leftAfter (gap::before) (2*far)))
        (2*IncrementSelector.blocksBits fields (4*retained+1))) =
      some (atLeftWord DecrementZero.breakOne (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[n+1]++fields++[0])) retained)) := by
  dsimp only
  let pos := head+1+IncrementSelector.cost (gap::before)+2+n
  have hr := IncrementMeaning.scan_leading Record285.machine DecrementZero.scan DecrementZero.check
    DecrementZero.breakOne DecrementZero.literal_scan_rows
    ((n+1)::foldRuns before []) gap (pos-1) far
    (2*IncrementSelector.blocksBits fields (4*retained+1))
  rw [← HalfOdd.odd_return_layout gap n before far,return_output gap n before fields retained] at hr
  have hc := DecrementNonzeroReturn.return_cost_exact gap before
  have hh : pos-1-(1+(completeCost ((n+1)::foldRuns before []) gap:Int)) = head-1 := by
    dsimp only [pos,completeCost]
    omega
  rw [hh] at hr
  exact hr

/-- Positive-even half operation through the full quotient, suffix shift and
the one-level break. The listed blank reserve pays for its quotient cycles. -/
theorem root_to_break (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let far := bits (pathLeft code) leftTail
    let carried := fields++List.replicate n 0
    let start := code.length+(2*gap+5)+pathCost code+
      IncrementSelector.cost blocks+2+cyclesCost n 0 fields
    let finish := 1+HalfEvenShift.shiftCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    silent Record285.machine (start+finish+back)
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*retained))))) =
      some (atLeftWord DecrementZero.breakOne (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[n+1]++carried++[0])) retained)) := by
  dsimp only
  let blocks := gap::before
  let far := bits (pathLeft code) leftTail
  let left := DecrementSelector.leftAfter blocks (2*far)
  let carried := fields++List.replicate n 0
  let pos := head+1+IncrementSelector.cost blocks+2+n
  let start := code.length+(2*gap+5)+pathCost code+
    IncrementSelector.cost blocks+2+cyclesCost n 0 fields
  let finish := 1+HalfEvenShift.shiftCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  have hc := HalfCycle.root_through_quotient_cycles code gap n 0 before fields hwalk head leftTail retained
  dsimp only at hc
  have hn : 2*n+0+2 = 2*n+2 := by omega
  rw [hn] at hc
  have he := HalfEvenShift.even_exit carried pos (pushBit n true (1+2*left)) retained
  have hr := return_to_break gap n before carried head far retained
  rw [show start+finish+back = start+(finish+back) by omega,silent_add,hc]
  simp only [Option.bind_some]
  rw [silent_add,he]
  simp only [Option.bind_some]
  exact hr

/-- Every positive even target has its exact quotient and returns silently
to the literal root via the skip-one control successor. -/
theorem root_returns_root (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let carried := fields++List.replicate n 0
    let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0]) retained
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+
      IncrementSelector.cost (gap::before)+2+cyclesCost n 0 fields
    let finish := 1+HalfEvenShift.shiftCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    let steps := start+finish+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    silent Record285.machine steps
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*retained))))) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let carried := fields++List.replicate n 0
  let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0]) retained
  let start := code.length+(2*gap+5)+pathCost code+
    IncrementSelector.cost (gap::before)+2+cyclesCost n 0 fields
  let finish := 1+HalfEvenShift.shiftCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  have hf := root_to_break code gap n before fields hwalk head leftTail retained
  dsimp only at hf
  have hbank : IncrementSelector.blocksBits (gap::(before++[n+1]++carried++[0])) retained =
      runPattern true (gap+1) false bank := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,bank]
  rw [hbank] at hf
  have hr := HalfEven.break_one_to_root code gap before.length hwalk head leftTail bank
  rw [show start+finish+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17) =
      (start+finish+back)+((3*(p.1+q.1)+2*gap+12)+(precode.length+17)) by omega,
    silent_add,hf]
  simp only [Option.bind_some]
  exact hr

theorem bound_root_returns_root_physical (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*retained))))) physical) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let carried := fields++List.replicate n 0
    let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0]) retained
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+
      IncrementSelector.cost (gap::before)+2+cyclesCost n 0 fields
    let finish := 1+HalfEvenShift.shiftCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    let steps := start+finish+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    returnPathSkipOne code = some (precode++[true]) ∧
    Rel (SymbolicDispatch.denote
      (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-q.1-2) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_returns_root code gap n before fields hwalk head leftTail retained)
  have hc := (HalfEven.half_control_preserves_root code before.length hwalk).2.2.1
  exact ⟨hc,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.HalfEvenPositive

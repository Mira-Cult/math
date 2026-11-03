import Shared.PNP.Record285.GrammarEndpoint

/-! Exact execution from the literal dispatcher root through any producer
increment path, followed by the complete physical increment and cleanup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch

/-- The full numeric tape at state 284, immediately after the root `110`,
before reading the grammar path. The unlisted tails are arbitrary. -/
def rootEntry (code : List Bool) (head : Int) (leftTail rightTail : Nat) :
    PhysicalNumeric.Config 285 :=
  denote (rightWord treeRoot (-(code.length:Int)) code false rootLeft []) head leftTail rightTail

/-- A checked grammar path is an exact finite, silent physical dispatch from
state 284 to its selected clean increment terminal. -/
theorem root_dispatch_increment (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i))
    (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (rootEntry code head leftTail rightTail) =
      some ⟨IncrementPreparation.terminal i,head,bits (pathLeft code) leftTail,false,rightTail⟩ := by
  have hr := (producer_increment_route code i hwalk).2
  have hs := route_scan code treeRoot (IncrementPreparation.terminal i) hr
    (-(code.length:Int)) false rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code false rootLeft [])
    ⟨IncrementPreparation.terminal i,0,code.reverse++rootLeft,false,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [rootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- Producer grammar path, physical root dispatch, increment, and cleanup
compose as one exact silent segment on the complete physical tape. -/
theorem root_through_increment_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained)))) physical) :
    let selected := gap::(before++[target])
    let n := (IncrementCleanup.peel (pathLeft code)).1
    let far := bits (IncrementCleanup.peel (pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := code.length + ((2*gap+5) + pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  let tail := 2*runPattern false gap true
    (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))
  let selected := gap::(before++[target])
  let n := (IncrementCleanup.peel (pathLeft code)).1
  let far := bits (IncrementCleanup.peel (pathLeft code)).2 leftTail
  let updated := IncrementSelector.blocksBits (before++[target+1])
    (IncrementSelector.blocksBits suffix retained)
  let middle := (2*gap+5) + pathCost code +
    2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
  let steps := (code.length+middle)+(3*n+2*gap+9)
  have hstart := root_dispatch_increment code before.length hwalk head leftTail tail
  obtain ⟨hi,hr⟩ := producer_increment_route code before.length hwalk
  have hterminal := IncrementCleanup.terminal_through_cleanup gap target before suffix hi code
    (DispatcherInvariant.all_increment_routes_checked code before.length hi hr) head leftTail retained
  have hexec : silent Record285.machine steps (rootEntry code head leftTail tail) =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap+2) true (2*updated))) := by
    dsimp only [steps]
    rw [show (code.length+middle)+(3*n+2*gap+9) =
      code.length+(middle+(3*n+2*gap+9)) by omega,silent_add,hstart]
    simp only [Option.bind_some]
    exact hterminal
  have hp := silent_physical Record285.machine _ physical hrel _ _ hexec
  refine ⟨hp.1,hp.2,?_⟩
  omega

/-- The frozen producer bytes and the literal root-to-increment physical
contract, combined without a grammar-text binding hypothesis. -/
theorem bound_root_through_increment_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained)))) physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    let selected := gap::(before++[target])
    let n := (IncrementCleanup.peel (pathLeft code)).1
    let far := bits (IncrementCleanup.peel (pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := code.length + ((2*gap+5) + pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps :=
  ⟨literal_typed_serialization, root_through_increment_physical gap target before suffix
    code hwalk head leftTail retained physical hrel⟩

end Shared.PNP.Record285.Grammar

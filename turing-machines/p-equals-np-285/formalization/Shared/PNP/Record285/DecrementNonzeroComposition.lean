import Shared.PNP.Record285.DecrementDispatch
import Shared.PNP.Record285.DecrementNonzeroScan
import Shared.PNP.Record285.DecrementZeroRoot

/-! Complete nonzero decrement dispatch, selection, and suffix scan. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroComposition
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.IncrementShift (atWord suffixBits)
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

/-- Any clean producer decrement path with a positive target scans through
all finite suffix fields and reaches the leftward shift. -/
theorem terminal_nonzero_to_shift (code : List Bool) (gap k : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) :
    let left := bits (pathLeft code) leftTail
    let blocks := gap::before
    let bank := IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)
    let targetHead := head+1+IncrementSelector.cost blocks
    let selectedLeft := DecrementSelector.leftAfter blocks (2*left)
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
      (2+DecrementNonzeroScan.scanCost k fields)
    silent Record285.machine steps
      ⟨decTerminal before.length,head,left,false,2*runPattern false gap true (2*bank)⟩ =
      some (atWord DecrementNonzeroScan.shift (targetHead+DecrementNonzeroScan.scanCost k fields)
        (DecrementNonzeroScan.scannedLeft k fields (4*selectedLeft+1)) (4*retained)) := by
  dsimp only
  let left := bits (pathLeft code) leftTail
  let blocks := gap::before
  let bank := IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)
  let targetHead := head+1+IncrementSelector.cost blocks
  let selectedLeft := DecrementSelector.leftAfter blocks (2*left)
  have ht := DecrementDispatch.terminal_to_target code gap (k+1) before hwalk head leftTail
    (suffixBits fields retained)
  have hs := DecrementNonzeroScan.target_to_shift fields k targetHead selectedLeft retained
  exact silent_compose Record285.machine _ _ _
    ((2*gap+5)+pathCost code+IncrementSelector.cost blocks)
    (2+DecrementNonzeroScan.scanCost k fields) ht hs

theorem terminal_nonzero_to_shift_physical (code : List Bool) (gap k : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained))⟩ physical) :
    let left := bits (pathLeft code) leftTail
    let blocks := gap::before
    let targetHead := head+1+IncrementSelector.cost blocks
    let selectedLeft := DecrementSelector.leftAfter blocks (2*left)
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
      (2+DecrementNonzeroScan.scanCost k fields)
    Rel (atWord DecrementNonzeroScan.shift (targetHead+DecrementNonzeroScan.scanCost k fields)
      (DecrementNonzeroScan.scannedLeft k fields (4*selectedLeft+1)) (4*retained))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (terminal_nonzero_to_shift code gap k before fields hwalk head leftTail retained)
  exact ⟨hp.1,hp.2,by omega⟩

/-- Root-to-shift form for any positive target, with the complete literal
configuration and no marked transition throughout the finite segment. -/
theorem root_nonzero_to_shift_physical (code : List Bool) (gap k : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)))) physical) :
    let left := bits (pathLeft code) leftTail
    let blocks := gap::before
    let targetHead := head+1+IncrementSelector.cost blocks
    let selectedLeft := DecrementSelector.leftAfter blocks (2*left)
    let inner := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
      (2+DecrementNonzeroScan.scanCost k fields)
    let steps := code.length+inner
    Rel (atWord DecrementNonzeroScan.shift (targetHead+DecrementNonzeroScan.scanCost k fields)
      (DecrementNonzeroScan.scannedLeft k fields (4*selectedLeft+1)) (4*retained))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  let tail := 2*runPattern false gap true
    (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained))
  let blocks := gap::before
  let inner := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
    (2+DecrementNonzeroScan.scanCost k fields)
  let targetHead := head+1+IncrementSelector.cost blocks
  let selectedLeft := DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail)
  have hr := DecrementZeroRoot.root_dispatch_decrement code before.length hwalk head leftTail tail
  have ht := terminal_nonzero_to_shift code gap k before fields hwalk head leftTail retained
  have he : silent Record285.machine (code.length+inner) (rootEntry code head leftTail tail) =
      some (atWord DecrementNonzeroScan.shift (targetHead+DecrementNonzeroScan.scanCost k fields)
        (DecrementNonzeroScan.scannedLeft k fields (4*selectedLeft+1)) (4*retained)) := by
    rw [silent_add,hr]
    simpa only [Option.bind_some] using ht
  have hp := silent_physical Record285.machine _ physical hrel _ _ he
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementNonzeroComposition

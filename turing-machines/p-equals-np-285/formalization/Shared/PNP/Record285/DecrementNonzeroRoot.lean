import Shared.PNP.Record285.DecrementNonzeroReturn
import Shared.PNP.Record285.DecrementControl

/-! Complete positive-target ordinary decrement through the literal root. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroRoot
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementPreparation (dispatch0)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

/-- A positive unary target is decremented and the complete machine returns
to state 284. One extra zero field precedes the untouched retained suffix. -/
theorem terminal_nonzero_returns_root (code : List Bool) (gap k : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let scan := DecrementNonzeroScan.scanCost k fields
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
      (2+completeCost (foldRuns fields []) k)+(1+completeCost (foldRuns before []) gap)+
      (3*p.1+2*gap+9)+(precode.length+17)
    silent Record285.machine steps
      ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
        2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained))⟩ =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  let scan := DecrementNonzeroScan.scanCost k fields
  let first := (2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
    (2+completeCost (foldRuns fields []) k)+(1+completeCost (foldRuns before []) gap)
  have hz := (decrement_reverse_zeros code before.length hwalk).1
  have hzcode : false ∈ code := by simpa using hz
  have hroot := IncrementCleanup.path_peel_preserves_root code hzcode
  have hroot' : peel (pathLeft code) = (p.1,p.2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hroot
  have hsafe := (producer_decrement_safe code before.length hwalk).2.2
  have hprefix := peel_prefix_safe code hsafe hz
  have hfirst := DecrementNonzeroReturn.terminal_nonzero_to_break code gap k before fields
    hwalk head leftTail retained
  have hleft := IncrementCleanup.path_peel_bits code leftTail
  rw [hroot'] at hleft
  have hbank : IncrementSelector.blocksBits (gap::(before++[k]++fields++[0])) retained =
      runPattern true (gap+1) false bank := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,bank]
  rw [hbank] at hfirst
  have hbreak : IncrementReturn.breakState = IncrementCleanup.lexical := rfl
  rw [hbreak] at hfirst
  have hcleanup := IncrementCleanup.literal_cleanup p.1 gap head (bits (p.2++rootLeft) leftTail) bank
  rw [← hleft] at hcleanup
  have hpref : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hword : 1+2*runPattern false (p.1+gap+2) true (2*bank) = 1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+gap+2 = (p.1+gap+1)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false]
    omega
  have hr := literal_return_root precode hprefix (head-p.1-1) leftTail rightTail
  have hpos : (head-p.1-1)-1 = head-p.1-2 := by omega
  rw [hpref,hpos,← hword] at hr
  have hcost : first+(3*p.1+2*gap+9)+(precode.length+17) =
      first+((3*p.1+2*gap+9)+(precode.length+17)) := by omega
  change silent Record285.machine (first+(3*p.1+2*gap+9)+(precode.length+17)) _ = _
  rw [hcost,silent_add]
  rw [hfirst]
  simp only [Option.bind_some]
  rw [silent_add,hcleanup]
  simp only [Option.bind_some]
  exact hr

/-- Full physical positive decrement from a clean grammar root to the next
root, with exact no-event progress and the skip-zero control successor. -/
theorem bound_root_nonzero_returns_root_physical (code : List Bool) (gap k : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)))) physical) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let scan := DecrementNonzeroScan.scanCost k fields
    let inner := (2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
      (2+completeCost (foldRuns fields []) k)+(1+completeCost (foldRuns before []) gap)+
      (3*p.1+2*gap+9)+(precode.length+17)
    let steps := code.length+inner
    Grammar.literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some (precode++[true]) ∧
    Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-1) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  let scan := DecrementNonzeroScan.scanCost k fields
  let inner := (2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
    (2+completeCost (foldRuns fields []) k)+(1+completeCost (foldRuns before []) gap)+
    (3*p.1+2*gap+9)+(precode.length+17)
  let tail := 2*runPattern false gap true
    (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained))
  have hd := DecrementZeroRoot.root_dispatch_decrement code before.length hwalk head leftTail tail
  have ht := terminal_nonzero_returns_root code gap k before fields hwalk head leftTail retained
  have he : silent Record285.machine (code.length+inner) (rootEntry code head leftTail tail) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
    rw [silent_add,hd]
    simpa only [Option.bind_some] using ht
  have hp := silent_physical Record285.machine _ physical hrel _ _ he
  have hz := (decrement_reverse_zeros code before.length hwalk).1
  have hc := return_after_zero code.reverse hz
  exact ⟨literal_typed_serialization,hc,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementNonzeroRoot

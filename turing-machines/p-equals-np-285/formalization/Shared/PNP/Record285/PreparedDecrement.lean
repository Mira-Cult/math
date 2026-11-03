import Shared.PNP.Record285.PreparedIncrement
import Shared.PNP.Record285.DecrementNextDispatch

/-! Connect already-prepared decrement terminals to the existing full-tape
zero and positive decrement proofs at their common selector boundary. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.PreparedDecrement
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

/-- Rejoin a verified silent execution at an identical full configuration. -/
theorem silent_rejoin (M : Machine 285) (first second middle final : PhysicalNumeric.Config 285)
    (a b c : Nat) (ha : silent M a first = some middle)
    (hab : silent M (a+b) first = some final) (hc : silent M c second = some middle) :
    silent M (c+b) second = some final := by
  rw [silent_add,ha] at hab
  simp only [Option.bind_some] at hab
  rw [silent_add,hc]
  simpa only [Option.bind_some] using hab

theorem root_dispatch_marked (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (markedRootEntry code head leftTail rightTail) =
      some ⟨decTerminal i,head,bits (pathLeft code) leftTail,true,rightTail⟩ := by
  have hr := (producer_decrement_safe code i hwalk).2.1
  have hs := route_scan code treeRoot (decTerminal i) hr
    (-(code.length:Int)) true rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code true rootLeft [])
    ⟨decTerminal i,0,code.reverse++rootLeft,true,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [markedRootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- The marked terminal reaches the exact selector configuration reached by
the unmarked terminal's preparation and redispatch. -/
theorem marked_to_selector (i gap : Nat) (hi : i < 15) (head : Int) (left tail : Nat) :
    silent Record285.machine 1
      ⟨decTerminal i,head,left,true,2*pushBit (gap+1) true tail⟩ =
      some ⟨DecrementPreparation.selector i,head+1,2*left,false,pushBit (gap+1) true tail⟩ := by
  have hr := (DecrementPreparation.terminal_rows i hi).2
  simp only [silent,PhysicalNumeric.step,hr,Bool.false_eq_true,if_false,bitVal,if_false,
    Nat.add_zero,even_bit,even_tail]

/-- Prepared-marked zero decrement reaches precisely the existing zero-case
root result; the entire branch is silent and has an explicit finite duration. -/
theorem marked_zero_returns_root (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let rest := 2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    silent Record285.machine (code.length+1+rest)
      (markedRootEntry code head leftTail (2*pushBit (gap+1) true (2*bank))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let bank := IncrementSelector.blocksBits (before++[0]) suffix
  let rest := 2*IncrementSelector.cost (gap::before)+4+
    (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
  let a := (2*gap+5)+pathCost code
  let left := bits (pathLeft code) leftTail
  have ha := DecrementDispatch.terminal_to_selector code before.length gap hwalk head leftTail (2*bank)
  have hfull := DecrementZeroRoot.terminal_zero_returns_root code gap before hwalk head leftTail suffix
  dsimp only at hfull
  have htime : (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12)+(precode.length+17) = a+rest := by
    dsimp [a,rest]; omega
  rw [htime] at hfull
  have hi := (producer_decrement_safe code before.length hwalk).1
  have hb := marked_to_selector before.length gap hi head left (2*bank)
  have hrest := silent_rejoin Record285.machine _ _ _ _ a rest 1 ha hfull hb
  have hd := root_dispatch_marked code before.length hwalk head leftTail (2*pushBit (gap+1) true (2*bank))
  rw [show code.length+1+rest = code.length+(1+rest) by omega,silent_add,hd]
  simpa only [Option.bind_some] using hrest

/-- Positive decrement rejoins the existing proof at the same selector. -/
theorem marked_nonzero_returns_root (code : List Bool) (gap k : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let initialBank := IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)
    let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let scan := DecrementNonzeroScan.scanCost k fields
    let rest := IncrementSelector.cost (gap::before)+(2+scan)+
      (2+IncrementReturn.completeCost (IncrementMeaning.foldRuns fields []) k)+
      (1+IncrementReturn.completeCost (IncrementMeaning.foldRuns before []) gap)+
      (3*p.1+2*gap+9)+(precode.length+17)
    silent Record285.machine (code.length+1+rest)
      (markedRootEntry code head leftTail (2*pushBit (gap+1) true (2*initialBank))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let initialBank := IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained)
  let scan := DecrementNonzeroScan.scanCost k fields
  let rest := IncrementSelector.cost (gap::before)+(2+scan)+
    (2+IncrementReturn.completeCost (IncrementMeaning.foldRuns fields []) k)+
    (1+IncrementReturn.completeCost (IncrementMeaning.foldRuns before []) gap)+
    (3*p.1+2*gap+9)+(precode.length+17)
  let a := (2*gap+5)+pathCost code
  let left := bits (pathLeft code) leftTail
  have ha := DecrementDispatch.terminal_to_selector code before.length gap hwalk head leftTail (2*initialBank)
  have hfull := DecrementNonzeroRoot.terminal_nonzero_returns_root code gap k before fields
    hwalk head leftTail retained
  dsimp only at hfull
  have htime : (2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)+(2+scan)+
      (2+IncrementReturn.completeCost (IncrementMeaning.foldRuns fields []) k)+
      (1+IncrementReturn.completeCost (IncrementMeaning.foldRuns before []) gap)+
      (3*p.1+2*gap+9)+(precode.length+17) = a+rest := by
    dsimp [a,rest]; omega
  rw [htime] at hfull
  have hi := (producer_decrement_safe code before.length hwalk).1
  have hb := marked_to_selector before.length gap hi head left (2*initialBank)
  have hrest := silent_rejoin Record285.machine _ _ _ _ a rest 1 ha hfull hb
  have hd := root_dispatch_marked code before.length hwalk head leftTail
    (2*pushBit (gap+1) true (2*initialBank))
  rw [show code.length+1+rest = code.length+(1+rest) by omega,silent_add,hd]
  simpa only [Option.bind_some] using hrest

/-- The marked layout has the same full-tape result and control successor as
the unmarked layout, for either branch of the decrement. -/
theorem marked_decrement_complete (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (markedRootEntry code head leftTail
      (2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained)))) physical) :
    DecrementComplete.resultControl code target =
      some (DecrementComplete.resultPrefix code target++[true]) ∧
    ∃ steps, 0 < steps ∧
      Rel (DecrementComplete.resultConfig code gap before fields head leftTail retained target)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases target with
  | zero =>
    have he := marked_zero_returns_root code gap before hwalk head leftTail (suffixBits fields retained)
    have hp := silent_physical Record285.machine _ physical hrel _ _ he
    have hc := decrement_control_preserves_root code before.length hwalk
    exact ⟨hc.2.2.1,_,by omega,hp.1,hp.2⟩
  | succ k =>
    have he := marked_nonzero_returns_root code gap k before fields hwalk head leftTail retained
    have hp := silent_physical Record285.machine _ physical hrel _ _ he
    have hz := (decrement_reverse_zeros code before.length hwalk).1
    have hc := return_after_zero code.reverse hz
    exact ⟨hc,_,by omega,hp.1,hp.2⟩

/-- Both explicit marker layouts return the same branch-specific complete
configuration and control successor. -/
theorem decrement_both_markers (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (marker : Bool) (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    DecrementComplete.resultControl code target =
      some (DecrementComplete.resultPrefix code target++[true]) ∧
    ∃ steps, 0 < steps ∧
      Rel (DecrementComplete.resultConfig code gap before fields head leftTail retained target)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  cases marker with
  | false =>
    simp only [Bool.false_eq_true,if_false] at hlayout
    rw [hlayout] at hrel
    exact DecrementComplete.root_decrement_complete code gap target before fields hwalk
      head leftTail retained physical hrel
  | true =>
    simp only [if_true] at hlayout
    rw [hlayout] at hrel
    exact marked_decrement_complete code gap target before fields hwalk head leftTail retained physical hrel

/-- The actual returned tape also supports a positive silent next dispatch. -/
theorem decrement_then_dispatch (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (marker : Bool) (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    DecrementComplete.resultControl code target =
      some (DecrementComplete.resultPrefix code target++[true]) ∧
    ∃ steps, 0 < steps ∧
      Rel (DecrementComplete.resultConfig code gap before fields head leftTail retained target)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      HalfComplete.NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  obtain ⟨hc,steps,hpos,hresult,hquiet⟩ := decrement_both_markers code gap target before fields
    hwalk marker head leftTail rightTail retained hlayout physical hrel
  have hroot := hresult
  rw [DecrementComplete.result_config_layout] at hroot
  have hn := HalfComplete.returned_root_dispatch _ _ _ _ _ hroot
  exact ⟨hc,steps,hpos,hresult,hn,hquiet⟩

end Shared.PNP.Record285.PreparedDecrement

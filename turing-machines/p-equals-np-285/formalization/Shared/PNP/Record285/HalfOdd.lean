import Shared.PNP.Record285.HalfCycle
import Shared.PNP.Record285.DecrementNonzeroReturn
import Shared.PNP.Record285.DecrementControl

/-! The odd-parity quotient exit through its first suffix shift. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfOdd
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost)
open Shared.PNP.Record285.IncrementReturn (completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft scanCost)
open Shared.PNP.Record285.HalfCycle
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.SymbolicDispatch (bits pathLeft pathCost)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

def continuation : Fin 285 := ⟨46,by decide⟩

theorem return_zero : Record285.machine.table.row returnState false =
    ⟨false,.right,continuation,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem zero_scan_layout (first : Nat) (rest : List Nat) (left : Nat) :
    scannedLeft 0 (first::rest) (4*left) =
      1+2*completeBits (foldRuns rest []) first (2*left) := by
  simp only [scannedLeft,pushBit]
  have h : 4*(4*left)+1 = 4*(2*(2*left))+1 := by omega
  rw [h]
  exact DecrementNonzeroLayout.scan_layout rest first (2*left)

theorem shift_empty (M : Machine 285) (qshift qcheck qret : Fin 285)
    (rows : DecrementNonzeroShift.Rows M qshift qcheck qret)
    (head : Int) (left retained : Nat) :
    silent M 2 (atWord qshift head (4*left) (4*retained)) =
      some (atLeftWord qret (head-2) (2*left) (2*(4*retained+1))) := by
  rw [show 4*left = 2*(2*left) by omega,show 4*retained = 2*(2*retained) by omega]
  simp only [atWord,atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,
    rows.scanZero,rows.checkZero,Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero]
  have hh : head-1-1 = head-2 := by omega
  have hr : 2*(2*(2*retained)+1) = 2*(4*retained+1) := by omega
  simp only [hh,hr]

def shiftCost : List Nat → Nat
  | [] => 2
  | first::rest => 2+completeCost (foldRuns rest []) first

/-- The odd exit scans and shifts all following fields, stopping at the
boundary with its complete tape and arbitrary retained suffix. -/
theorem scan_shift (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (scanCost 0 fields+shiftCost fields)
      (atWord scan head (4*left) (runPattern true 0 false (suffixBits fields retained))) =
      some (atLeftWord returnState (head-2) (2*left)
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  have hs := DecrementNonzeroScan.scan_suffix Record285.machine scan check shift
    scan_rows fields 0 head (4*left) retained
  cases fields with
  | nil =>
    have he := shift_empty Record285.machine shift shiftCheck returnState shift_rows head left retained
    simp only [scannedLeft,pushBit,IncrementSelector.blocksBits,shiftCost,scanCost,
      IncrementShift.cost] at hs ⊢
    rw [silent_add,hs]
    simp only [Option.bind_some]
    have hh : head+((0+1+1:Nat):Int)-2 = head := by omega
    simpa only [hh] using he
  | cons first rest =>
    have hl := zero_scan_layout first rest left
    rw [hl] at hs
    let total := scanCost 0 (first::rest)
    let runs := foldRuns rest []
    have he := DecrementNonzeroShiftRun.shift_entry Record285.machine shift shiftCheck
      returnState shift_rows (head+total-2) (completeBits runs first (2*left)) retained
    have ht := DecrementNonzeroShift.shift_complete Record285.machine shift shiftCheck
      returnState shift_rows runs first (head+total-4) (2*left) (8*retained+2)
    rw [DecrementNonzeroLayout.shifted_output rest first retained] at ht
    have hc : total = completeCost runs first+2 := by
      dsimp only [total,runs,scanCost]
      simp only [IncrementShift.cost,IncrementMeaning.folded_cost,completeCost,IncrementMeaning.shift_cost]
      omega
    have hh : head+(total:Int)-4-(completeCost runs first:Int) = head-2 := by omega
    simp only [shiftCost]
    rw [silent_add,hs]
    simp only [Option.bind_some]
    rw [silent_add,he]
    simp only [Option.bind_some]
    have hh' : head+(total:Int)-2-2 = head+(total:Int)-4 := by omega
    rw [hh']
    simpa only [hh] using ht

theorem enter_odd (M : Machine 285) (qboundary qnext qscan : Fin 285)
    (h1 : M.table.row qboundary true = ⟨false,.right,qnext,false⟩)
    (h2 : M.table.row qnext true = ⟨false,.right,qscan,false⟩)
    (head : Int) (left tail : Nat) :
    silent M 2 ⟨qboundary,head,left,true,runPattern true 1 false tail⟩ =
      some (atWord qscan (head+2) (4*left) (runPattern true 0 false tail)) := by
  simp only [silent,PhysicalNumeric.step,h1,h2,Bool.false_eq_true,if_false,bitVal,
    Nat.add_zero,runPattern_succ_read,runPattern_succ_tail,runPattern_zero_read,runPattern_zero_tail,atWord]
  have hh : head+1+1 = head+2 := by omega
  have hl : 2*(2*left) = 4*left := by omega
  simp only [hh,hl]

theorem exit_return (M : Machine 285) (qret qnext : Fin 285)
    (hrow : M.table.row qret false = ⟨false,.right,qnext,false⟩)
    (head : Int) (left bank : Nat) :
    silent M 1 (atLeftWord qret head (2*left) (2*bank)) =
      some ⟨qnext,head+1,2*left,false,bank⟩ := by
  simp only [atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,hrow,
    Bool.false_eq_true,if_false,bitVal,Nat.add_zero]

/-- With exactly one unprocessed unit after the current bit, the literal
odd exit removes it, shifts the full following bank, and reaches the next
return phase. This still precedes the final return to the grammar root. -/
theorem odd_exit (fields : List Nat) (head : Int) (left retained : Nat) :
    let cost := 2+scanCost 0 fields+shiftCost fields+1
    silent Record285.machine cost
      ⟨boundary,head,1+2*left,true,runPattern true 1 false (suffixBits fields retained)⟩ =
      some ⟨continuation,head+1,2*(1+2*left),false,
        IncrementSelector.blocksBits fields (4*retained+1)⟩ := by
  dsimp only
  let total := scanCost 0 fields+shiftCost fields
  have he := enter_odd Record285.machine boundary next scan boundary_one next_one
    head (1+2*left) (suffixBits fields retained)
  have hs := scan_shift fields (head+2) (1+2*left) retained
  have hh : head+2-2 = head := by omega
  rw [hh] at hs
  have hr := exit_return Record285.machine returnState continuation return_zero head (1+2*left)
    (IncrementSelector.blocksBits fields (4*retained+1))
  rw [show 2+scanCost 0 fields+shiftCost fields+1 = 2+(total+1) by dsimp [total]; omega,
    silent_add,he]
  simp only [Option.bind_some]
  rw [silent_add,hs]
  simp only [Option.bind_some]
  exact hr

/-- The shared decrement scanner makes the odd exit's second shift. The
nonempty field list includes the zero field just appended by the first shift. -/
theorem second_shift (first : Nat) (rest : List Nat) (head : Int) (left retained : Nat) :
    let fields := first::rest
    let total := scanCost 0 fields
    let back := completeCost (foldRuns rest []) first
    silent Record285.machine (total+2+back)
      (atWord DecrementNonzeroScan.scan head (2*left)
        (runPattern true 0 false (suffixBits fields retained))) =
      some (atLeftWord DecrementNonzeroShift.returnState (head-2) left
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  dsimp only
  let fields := first::rest
  let total := scanCost 0 fields
  let runs := foldRuns rest []
  let back := completeCost runs first
  have hs := DecrementNonzeroScan.scan_suffix Record285.machine DecrementNonzeroScan.scan
    DecrementNonzeroScan.check DecrementNonzeroScan.shift DecrementNonzeroScan.literal_rows
    fields 0 head (2*left) retained
  have hl : scannedLeft 0 fields (2*left) = 1+2*completeBits runs first left := by
    dsimp only [fields,runs,scannedLeft,pushBit]
    exact DecrementNonzeroLayout.scan_layout rest first left
  rw [hl] at hs
  have he := DecrementNonzeroShiftRun.shift_entry Record285.machine DecrementNonzeroScan.shift
    DecrementNonzeroShift.check DecrementNonzeroShift.returnState DecrementNonzeroShift.literal_rows
    (head+total-2) (completeBits runs first left) retained
  have ht := DecrementNonzeroShift.shift_complete Record285.machine DecrementNonzeroScan.shift
    DecrementNonzeroShift.check DecrementNonzeroShift.returnState DecrementNonzeroShift.literal_rows
    runs first (head+total-4) left (8*retained+2)
  rw [DecrementNonzeroLayout.shifted_output rest first retained] at ht
  change silent Record285.machine back _ = _ at ht
  have hc : total = back+2 := by
    dsimp only [total,fields,back,runs,scanCost]
    simp only [IncrementShift.cost,IncrementMeaning.folded_cost,completeCost,IncrementMeaning.shift_cost]
    omega
  have hh : head+(total:Int)-4-(back:Int) = head-2 := by omega
  change head+(total:Int)-4-(completeCost runs first:Int) = head-2 at hh
  rw [show total+2+back = total+(2+back) by omega,silent_add,hs]
  simp only [Option.bind_some]
  rw [silent_add,he]
  simp only [Option.bind_some]
  have hh' : head+(total:Int)-2-2 = head+(total:Int)-4 := by omega
  rw [hh']
  simpa only [hh] using ht

def secondCost : List Nat → Nat
  | [] => scanCost 0 [0]+2+completeCost (foldRuns [] []) 0
  | first::rest => scanCost 0 (first::(rest++[0]))+2+
      completeCost (foldRuns (rest++[0]) []) first

theorem second_shift_appended (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (secondCost fields)
      (atWord DecrementNonzeroScan.scan head (2*left)
        (runPattern true 0 false (suffixBits (fields++[0]) retained))) =
      some (atLeftWord DecrementNonzeroShift.returnState (head-2) left
        (2*IncrementSelector.blocksBits (fields++[0]) (4*retained+1))) := by
  cases fields with
  | nil => exact second_shift 0 [] head left retained
  | cons first rest =>
    simpa only [List.cons_append,secondCost] using second_shift first (rest++[0]) head left retained

/-- Odd quotient exit through both complete suffix shifts and into the
shared return scanner. One additional blank is reserved beyond the finite
bank; all cells above that blank are retained exactly. -/
theorem odd_exit_to_return (fields : List Nat) (head : Int) (left retained : Nat) :
    let steps := (2+scanCost 0 fields+shiftCost fields+1)+secondCost fields
    silent Record285.machine steps
      ⟨boundary,head,1+2*left,true,runPattern true 1 false (suffixBits fields (2*retained))⟩ =
      some (atLeftWord DecrementNonzeroShift.returnState (head-1) (1+2*left)
        (2*IncrementSelector.blocksBits (fields++[0]) (4*retained+1))) := by
  dsimp only
  let bank := suffixBits (fields++[0]) retained
  let total := 2+scanCost 0 fields+shiftCost fields+1
  have ho := odd_exit fields head left (2*retained)
  dsimp only at ho
  rw [suffix_append_zero] at ho
  have hs := second_shift_appended fields (head+1) (1+2*left) retained
  have hin : atWord DecrementNonzeroScan.scan (head+1) (2*(1+2*left))
      (runPattern true 0 false bank) =
      ⟨continuation,head+1,2*(1+2*left),false,bank⟩ := by
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,atWord,even_bit,even_tail]
    rfl
  rw [hin] at hs
  have hh : head+1-2 = head-1 := by omega
  rw [hh] at hs
  rw [silent_add,ho]
  simp only [Option.bind_some]
  exact hs

/-- All odd targets at least three reach the shared return scanner from a
clean root. The number of reserved zeros pays for every shift. -/
theorem root_odd_to_return (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let left := DecrementSelector.leftAfter blocks
      (2*SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail)
    let start := code.length+(2*gap+5)+SymbolicDispatch.pathCost code+
      IncrementSelector.cost blocks+2+cyclesCost n 1 fields
    let carried := fields++List.replicate n 0
    let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
    let pos := head+1+IncrementSelector.cost blocks+2+n
    silent Record285.machine (start+finish)
      (Grammar.rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+3])
            (suffixBits fields (2^n*(2*retained)))))) =
      some (atLeftWord DecrementNonzeroShift.returnState (pos-1)
        (1+2*pushBit n true (1+2*left))
        (2*IncrementSelector.blocksBits (carried++[0]) (4*retained+1))) := by
  dsimp only
  let blocks := gap::before
  let left := DecrementSelector.leftAfter blocks
    (2*SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail)
  let carried := fields++List.replicate n 0
  let pos := head+1+IncrementSelector.cost blocks+2+n
  let start := code.length+(2*gap+5)+SymbolicDispatch.pathCost code+
    IncrementSelector.cost blocks+2+cyclesCost n 1 fields
  let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
  have hc := root_through_quotient_cycles code gap n 1 before fields hwalk head leftTail (2*retained)
  dsimp only at hc
  have hn : 2*n+1+2 = 2*n+3 := by omega
  rw [hn] at hc
  have he := odd_exit_to_return carried pos (pushBit n true (1+2*left)) retained
  dsimp only at he
  rw [silent_add,hc]
  simp only [Option.bind_some]
  exact he

theorem root_odd_to_return_physical (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (Grammar.rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[2*n+3])
          (suffixBits fields (2^n*(2*retained)))))) physical) :
    let blocks := gap::before
    let left := DecrementSelector.leftAfter blocks
      (2*SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail)
    let start := code.length+(2*gap+5)+SymbolicDispatch.pathCost code+
      IncrementSelector.cost blocks+2+cyclesCost n 1 fields
    let carried := fields++List.replicate n 0
    let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
    let pos := head+1+IncrementSelector.cost blocks+2+n
    let steps := start+finish
    Rel (atLeftWord DecrementNonzeroShift.returnState (pos-1)
      (1+2*pushBit n true (1+2*left))
      (2*IncrementSelector.blocksBits (carried++[0]) (4*retained+1)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_odd_to_return code gap n before fields hwalk head leftTail retained)
  exact ⟨hp.1,hp.2,by omega⟩

theorem odd_return_layout (gap n : Nat) (before : List Nat) (far : Nat) :
    1+2*pushBit n true (1+2*DecrementSelector.leftAfter (gap::before) (2*far)) =
      1+2*completeBits ((n+1)::foldRuns before []) gap far := by
  rw [DecrementNonzeroReturn.selected_left_exact]
  have hbase : 1+2*(2*(1+2*completeBits (foldRuns before []) gap far)) =
      1+2*completeBits (0::foldRuns before []) gap far := by
    simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  rw [hbase,DecrementNonzeroLayout.push_ones_cons]
  simp only [completeBits,runPattern,bitVal,if_true]

/-- Reconstruct the complete bank while the shared return scanner moves
left across the quotient and all preceding fields. -/
theorem odd_return_output (gap n : Nat) (before fields : List Nat) (retained : Nat) :
    completeRight ((n+1)::foldRuns before []) gap
      (2*(2*IncrementSelector.blocksBits (fields++[0]) (4*retained+1))+1) =
    4*IncrementSelector.blocksBits
      (gap::(before++[n+1]++fields++[0,0])) retained := by
  rw [IncrementMeaning.scan_output]
  simp only [IncrementMeaning.backFold]
  rw [IncrementMeaning.backFold_foldRuns]
  simp only [IncrementMeaning.backFold,← IncrementMeaning.blocks_cons,← IncrementMeaning.blocks_append]
  have hz : 4*retained+1 = IncrementSelector.blocksBits [0] retained := by
    simp [IncrementSelector.blocksBits,runPattern,bitVal]; omega
  rw [hz,← IncrementMeaning.blocks_append]
  congr 2
  simp [List.append_assoc]

theorem odd_return_to_break (gap n : Nat) (before fields : List Nat)
    (head : Int) (far retained : Nat) :
    let pos := head+1+IncrementSelector.cost (gap::before)+2+n
    let steps := 1+completeCost ((n+1)::foldRuns before []) gap
    silent Record285.machine steps
      (atLeftWord DecrementNonzeroShift.returnState (pos-1)
        (1+2*pushBit n true (1+2*DecrementSelector.leftAfter (gap::before) (2*far)))
        (2*IncrementSelector.blocksBits (fields++[0]) (4*retained+1))) =
      some (atLeftWord IncrementReturn.breakState (head-1) far
        (4*IncrementSelector.blocksBits
          (gap::(before++[n+1]++fields++[0,0])) retained)) := by
  dsimp only
  let pos := head+1+IncrementSelector.cost (gap::before)+2+n
  have hr := IncrementMeaning.scan_leading Record285.machine IncrementShift.returnState
    IncrementReturn.checkState IncrementReturn.breakState IncrementReturn.literal_rows
    ((n+1)::foldRuns before []) gap (pos-1) far
    (2*IncrementSelector.blocksBits (fields++[0]) (4*retained+1))
  rw [← odd_return_layout gap n before far,odd_return_output gap n before fields retained] at hr
  have hc := DecrementNonzeroReturn.return_cost_exact gap before
  have hh : pos-1-(1+(completeCost ((n+1)::foldRuns before []) gap:Int)) = head-1 := by
    dsimp only [pos,completeCost]
    omega
  rw [hh] at hr
  exact hr

theorem half_path_zero (code : List Bool) (i : Nat)
    (hwalk : Grammar.walk 162 code = some (.half i)) : false ∈ code := by
  cases code with
  | nil => simp [Grammar.walk] at hwalk
  | cons a as =>
    cases a with
    | false => simp
    | true =>
      cases as with
      | nil => simp [Grammar.walk,Grammar.root_true_edge] at hwalk
      | cons b bs =>
        cases b with
        | false => simp
        | true => cases bs <;>
          simp [Grammar.walk,Grammar.root_true_edge,Grammar.next_true_edge] at hwalk

theorem root_odd_to_break (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let far := SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail
    let carried := fields++List.replicate n 0
    let start := code.length+(2*gap+5)+SymbolicDispatch.pathCost code+
      IncrementSelector.cost blocks+2+cyclesCost n 1 fields
    let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    silent Record285.machine (start+finish+back)
      (Grammar.rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+3])
            (suffixBits fields (2^n*(2*retained)))))) =
      some (atLeftWord IncrementReturn.breakState (head-1) far
        (4*IncrementSelector.blocksBits
          (gap::(before++[n+1]++carried++[0,0])) retained)) := by
  dsimp only
  let blocks := gap::before
  let far := SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail
  let carried := fields++List.replicate n 0
  let start := code.length+(2*gap+5)+SymbolicDispatch.pathCost code+
    IncrementSelector.cost blocks+2+cyclesCost n 1 fields
  let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  have ho := root_odd_to_return code gap n before fields hwalk head leftTail retained
  have hr := odd_return_to_break gap n before carried head far retained
  rw [silent_add,ho]
  simp only [Option.bind_some]
  exact hr

/-- For every odd target at least three, complete the literal half operation
from root to root. The quotient is `n+1`; the complete high tape, `n+2`
new zero fields, and skip-zero control successor are given explicitly. -/
theorem root_odd_returns_root (code : List Bool) (gap n : Nat) (before fields : List Nat)
    (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let carried := fields++List.replicate n 0
    let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0,0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+
      IncrementSelector.cost (gap::before)+2+cyclesCost n 1 fields
    let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    let steps := start+finish+back+(3*p.1+2*gap+9)+(precode.length+17)
    silent Record285.machine steps
      (Grammar.rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+3])
            (suffixBits fields (2^n*(2*retained)))))) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let carried := fields++List.replicate n 0
  let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0,0]) retained
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  let start := code.length+(2*gap+5)+pathCost code+
    IncrementSelector.cost (gap::before)+2+cyclesCost n 1 fields
  let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
  let back := 1+completeCost ((n+1)::foldRuns before []) gap
  have hzcode := half_path_zero code before.length hwalk
  have hz : false ∈ code.reverse := by simpa using hzcode
  have hroot := IncrementCleanup.path_peel_preserves_root code hzcode
  have hroot' : peel (pathLeft code) = (p.1,p.2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hroot
  have hsafe := (producer_half_safe code before.length hwalk).2.2
  have hprefix := peel_prefix_safe code hsafe hz
  have hfirst := root_odd_to_break code gap n before fields hwalk head leftTail retained
  dsimp only at hfirst
  have hleft := IncrementCleanup.path_peel_bits code leftTail
  rw [hroot'] at hleft
  have hbank : IncrementSelector.blocksBits (gap::(before++[n+1]++carried++[0,0])) retained =
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
  rw [show start+finish+back+(3*p.1+2*gap+9)+(precode.length+17) =
      (start+finish+back)+((3*p.1+2*gap+9)+(precode.length+17)) by omega,
    silent_add,hfirst]
  simp only [Option.bind_some]
  rw [silent_add,hcleanup]
  simp only [Option.bind_some]
  exact hr

/-- The frozen grammar, odd quotient, exact root-to-root physical execution,
and skip-zero control update, with positive progress and no marked events. -/
theorem bound_root_odd_returns_root_physical (code : List Bool) (gap n : Nat)
    (before fields : List Nat) (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (Grammar.rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[2*n+3])
          (suffixBits fields (2^n*(2*retained)))))) physical) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let carried := fields++List.replicate n 0
    let bank := IncrementSelector.blocksBits (before++[n+1]++carried++[0,0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+
      IncrementSelector.cost (gap::before)+2+cyclesCost n 1 fields
    let finish := 2+scanCost 0 carried+shiftCost carried+1+secondCost carried
    let back := 1+completeCost ((n+1)::foldRuns before []) gap
    let steps := start+finish+back+(3*p.1+2*gap+9)+(precode.length+17)
    Grammar.literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some (precode++[true]) ∧
    Rel (SymbolicDispatch.denote
      (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-1) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_odd_returns_root code gap n before fields hwalk head leftTail retained)
  have hz : false ∈ code.reverse := by simpa using half_path_zero code before.length hwalk
  have hc := return_after_zero code.reverse hz
  exact ⟨literal_typed_serialization,hc,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.HalfOdd

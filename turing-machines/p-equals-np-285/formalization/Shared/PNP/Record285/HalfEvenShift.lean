import Shared.PNP.Record285.HalfEven

/-! Full suffix scan and shift for the positive-even half exit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfEvenShift
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (atWord suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft scanCost)
attribute [local irreducible] Record285.machine

def scan : Fin 285 := ⟨63,by decide⟩
def check : Fin 285 := ⟨64,by decide⟩
def shift : Fin 285 := ⟨65,by decide⟩
def shiftCheck : Fin 285 := ⟨66,by decide⟩

theorem scan_rows : DecrementNonzeroScan.Rows Record285.machine scan check shift := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem shift_rows : DecrementNonzeroShift.Rows Record285.machine shift shiftCheck DecrementZero.scan := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem second_shift (first : Nat) (rest : List Nat) (head : Int) (left retained : Nat) :
    let fields := first::rest
    let total := scanCost 0 fields
    let back := completeCost (foldRuns rest []) first
    silent Record285.machine (total+2+back)
      (atWord scan head (2*left) (runPattern true 0 false (suffixBits fields retained))) =
      some (atLeftWord DecrementZero.scan (head-2) left
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  dsimp only
  let fields := first::rest
  let total := scanCost 0 fields
  let runs := foldRuns rest []
  let back := completeCost runs first
  have hs := DecrementNonzeroScan.scan_suffix Record285.machine scan check shift scan_rows
    fields 0 head (2*left) retained
  have hl : scannedLeft 0 fields (2*left) = 1+2*completeBits runs first left := by
    dsimp only [fields,runs,scannedLeft,pushBit]
    exact DecrementNonzeroLayout.scan_layout rest first left
  rw [hl] at hs
  have he := DecrementNonzeroShiftRun.shift_entry Record285.machine shift shiftCheck
    DecrementZero.scan shift_rows (head+total-2) (completeBits runs first left) retained
  have ht := DecrementNonzeroShift.shift_complete Record285.machine shift shiftCheck
    DecrementZero.scan shift_rows runs first (head+total-4) left (8*retained+2)
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

def shiftCost : List Nat → Nat
  | [] => scanCost 0 []+2
  | first::rest => scanCost 0 (first::rest)+2+completeCost (foldRuns rest []) first

theorem scan_shift (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (shiftCost fields)
      (atWord scan head (2*(1+2*left))
        (runPattern true 0 false (suffixBits fields retained))) =
      some (atLeftWord DecrementZero.scan (head-2) (1+2*left)
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  cases fields with
  | nil =>
    have hs := DecrementNonzeroScan.scan_suffix Record285.machine scan check shift scan_rows
      [] 0 head (2*(1+2*left)) retained
    have he := HalfOne.empty_shift Record285.machine shift shiftCheck DecrementZero.scan shift_rows
      head left retained
    simp only [shiftCost,scannedLeft,pushBit,IncrementSelector.blocksBits,scanCost,
      IncrementShift.cost] at hs ⊢
    rw [silent_add,hs]
    simp only [Option.bind_some]
    have hh : head+((0+1+1:Nat):Int)-2 = head := by omega
    simpa only [hh] using he
  | cons first rest => exact second_shift first rest head (1+2*left) retained

/-- Two states with the same current row have identical positive-time
behavior from otherwise identical configurations. -/
theorem swap_current_row (M : Machine 285) (a b : Fin 285) (hrow : M.table.row a false = M.table.row b false)
    (n : Nat) (hn : 0 < n) (head : Int) (left right : Nat) :
    silent M n ⟨a,head,left,false,right⟩ = silent M n ⟨b,head,left,false,right⟩ := by
  cases n with
  | zero => omega
  | succ n => simp only [silent,PhysicalNumeric.step,hrow]; rfl

theorem equal_zero_rows : Record285.machine.table.row HalfCycle.next false =
    Record285.machine.table.row scan false := by
  simp only [ArtifactEndpoint.literal_rows]
  decide

theorem shift_cost_pos (fields : List Nat) : 0 < shiftCost fields := by
  cases fields <;> simp only [shiftCost] <;> omega

theorem enter_even (M : Machine 285) (qboundary qnext : Fin 285)
    (hrow : M.table.row qboundary true = ⟨false,.right,qnext,false⟩)
    (head : Int) (left tail : Nat) :
    silent M 1 ⟨qboundary,head,1+2*left,true,runPattern true 0 false tail⟩ =
      some (atWord qnext (head+1) (2*(1+2*left)) (runPattern true 0 false tail)) := by
  simp only [runPattern,Shared.PNP.Record285.RelativeTape.bitVal,Bool.false_eq_true,if_false,Nat.zero_add,
    silent,PhysicalNumeric.step,hrow,atWord,Shared.PNP.Record285.IncrementShift.even_bit,
    Shared.PNP.Record285.IncrementShift.even_tail]
  simp only [Nat.add_zero]

/-- A positive even quotient exit shifts every following field and enters
the one-level return scanner with the entire tape explicit. -/
theorem even_exit (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (1+shiftCost fields)
      ⟨HalfCycle.boundary,head,1+2*left,true,runPattern true 0 false (suffixBits fields retained)⟩ =
      some (atLeftWord DecrementZero.scan (head-1) (1+2*left)
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  have he := enter_even Record285.machine HalfCycle.boundary HalfCycle.next HalfCycle.boundary_one
    head left (suffixBits fields retained)
  have hs := scan_shift fields (head+1) left retained
  have hword : atWord HalfCycle.next (head+1) (2*(1+2*left))
      (runPattern true 0 false (suffixBits fields retained)) =
      ⟨HalfCycle.next,head+1,2*(1+2*left),false,suffixBits fields retained⟩ := by
    simp [atWord,runPattern,Shared.PNP.Record285.RelativeTape.bitVal]
  have hword' : atWord scan (head+1) (2*(1+2*left))
      (runPattern true 0 false (suffixBits fields retained)) =
      ⟨scan,head+1,2*(1+2*left),false,suffixBits fields retained⟩ := by
    simp [atWord,runPattern,Shared.PNP.Record285.RelativeTape.bitVal]
  have hswap := swap_current_row Record285.machine HalfCycle.next scan equal_zero_rows
    (shiftCost fields) (shift_cost_pos fields) (head+1) (2*(1+2*left)) (suffixBits fields retained)
  rw [← hword,← hword'] at hswap
  rw [← hswap] at hs
  have hh : head+1-2 = head-1 := by omega
  rw [hh] at hs
  rw [silent_add,he]
  simp only [Option.bind_some]
  exact hs

end Shared.PNP.Record285.HalfEvenShift

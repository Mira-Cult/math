import Shared.PNP.Record285.HalfTarget
import Shared.PNP.Record285.DecrementNonzeroShiftRun

/-! The native-half quotient cycle, using the shared full-tape suffix scan
and shift. No claim about complete division or source reachability is made. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfCycle
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.SymbolicDispatch (bits pathCost pathLeft)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft scanCost)
open Shared.PNP.Record285.DecrementNonzeroShift (shiftedRight)
attribute [local irreducible] Record285.machine

def scan : Fin 285 := ⟨59,by decide⟩
def check : Fin 285 := ⟨60,by decide⟩
def shift : Fin 285 := ⟨61,by decide⟩
def shiftCheck : Fin 285 := ⟨62,by decide⟩
def returnState : Fin 285 := ⟨58,by decide⟩
def boundary : Fin 285 := ⟨67,by decide⟩
def next : Fin 285 := ⟨69,by decide⟩
def restore : Fin 285 := ⟨57,by decide⟩

theorem scan_rows : DecrementNonzeroScan.Rows Record285.machine scan check shift := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem shift_rows : DecrementNonzeroShift.Rows Record285.machine shift shiftCheck returnState := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem boundary_one : Record285.machine.table.row boundary true = ⟨false,.right,next,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem next_one : Record285.machine.table.row next true = ⟨false,.right,scan,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem return_one : Record285.machine.table.row returnState true = ⟨true,.right,restore,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem restore_zero : Record285.machine.table.row restore false = ⟨true,.right,boundary,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

/-- The left side of a scan with at least one unprocessed unary bit is the
exact reverse field list expected by the previously verified shifter. -/
theorem scan_layout (fields : List Nat) (k left : Nat) :
    scannedLeft (k+1) fields (4*left) =
      1+2*completeBits (foldRuns fields []) k left := by
  have hfirst : pushBit (k+1) true (4*left) = 1+2*completeBits [] k left := by
    induction k with
    | zero => simp [pushBit,completeBits,runPattern,bitVal]; omega
    | succ k ih =>
      rw [pushBit,pushBit_affine,ih]
      simp only [completeBits,runPattern,bitVal,if_true]
      omega
  cases fields with
  | nil => simpa only [scannedLeft,foldRuns] using hfirst
  | cons n rest =>
    simp only [scannedLeft,foldRuns]
    rw [hfirst]
    have h : 4*(1+2*completeBits [] k left)+1 =
        1+2*completeBits [0] k left := by
      simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
      omega
    rw [h]
    exact DecrementNonzeroLayout.scan_layout_aux rest n [] k left

/-- One complete forward scan and reverse shift when an unprocessed unary
bit remains. The entire high suffix is retained after one new zero field. -/
theorem scan_shift (fields : List Nat) (k : Nat) (head : Int) (left retained : Nat) :
    let cost := scanCost (k+1) fields + 2 + completeCost (foldRuns fields []) k
    silent Record285.machine cost
      (atWord scan head (4*left) (runPattern true (k+1) false (suffixBits fields retained))) =
      some (atLeftWord returnState (head-3) left
        (2*IncrementSelector.blocksBits (k::fields) (4*retained+1))) := by
  dsimp only
  let runs := foldRuns fields []
  let total := scanCost (k+1) fields
  have hs := DecrementNonzeroScan.scan_suffix Record285.machine scan check shift
    scan_rows fields (k+1) head (4*left) retained
  rw [scan_layout fields k left] at hs
  have he := DecrementNonzeroShiftRun.shift_entry Record285.machine shift shiftCheck
    returnState shift_rows (head+total-2) (completeBits runs k left) retained
  have ht := DecrementNonzeroShift.shift_complete Record285.machine shift shiftCheck
    returnState shift_rows runs k (head+total-4) left (8*retained+2)
  rw [DecrementNonzeroLayout.shifted_output fields k retained] at ht
  have hcost : total = completeCost runs k+1 := by
    dsimp only [total,runs,scanCost]
    simp only [IncrementMeaning.folded_cost,completeCost,IncrementMeaning.shift_cost]
    omega
  have hh : head+(total:Int)-4-(completeCost runs k:Int) = head-3 := by omega
  rw [show total+2+completeCost runs k = total+(2+completeCost runs k) by omega,
    silent_add,hs]
  simp only [Option.bind_some]
  rw [silent_add,he]
  simp only [Option.bind_some]
  have heq : head+(total:Int)-2-2 = head+(total:Int)-4 := by omega
  rw [heq]
  simpa only [hh] using ht

theorem enter_cycle (M : Machine 285) (qboundary qnext qscan : Fin 285)
    (h1 : M.table.row qboundary true = ⟨false,.right,qnext,false⟩)
    (h2 : M.table.row qnext true = ⟨false,.right,qscan,false⟩)
    (k : Nat) (head : Int) (left tail : Nat) :
    silent M 2 ⟨qboundary,head,1+2*left,true,runPattern true (k+2) false tail⟩ =
      some (atWord qscan (head+2) (4*(1+2*left)) (runPattern true (k+1) false tail)) := by
  simp only [silent,PhysicalNumeric.step,h1,h2,Bool.false_eq_true,if_false,bitVal,
    Nat.add_zero,runPattern_succ_read,runPattern_succ_tail,atWord]
  have hh : head+1+1 = head+2 := by omega
  have hl : 2*(2*(1+2*left)) = 4*(1+2*left) := by omega
  simp only [hh,hl]

theorem finish_cycle (M : Machine 285) (qret qrestore qboundary : Fin 285)
    (h1 : M.table.row qret true = ⟨true,.right,qrestore,false⟩)
    (h2 : M.table.row qrestore false = ⟨true,.right,qboundary,false⟩)
    (fields : List Nat) (k : Nat) (head : Int) (left retained : Nat) :
    silent M 2 (atLeftWord qret (head-1) (1+2*left)
      (2*IncrementSelector.blocksBits (k::fields) (4*retained+1))) =
      some ⟨qboundary,head+1,3+4*left,true,
        runPattern true k false (IncrementSelector.blocksBits fields (4*retained+1))⟩ := by
  simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,h1,h2,
    Bool.false_eq_true,if_false,bitVal,if_true,even_bit,even_tail]
  simp only [IncrementSelector.blocksBits,odd_bit,odd_tail]
  have hh : head-1+1+1 = head+1 := by omega
  have hl : 2*(2*left+1)+1 = 3+4*left := by omega
  simp only [hh,hl]

/-- A nonfinal quotient cycle removes two unprocessed units and adds one
quotient unit. Its finite suffix is shifted left, retaining all listed
fields and adding one zero field before the arbitrary high suffix. -/
theorem quotient_cycle (fields : List Nat) (k : Nat) (head : Int) (left retained : Nat) :
    let cost := 4 + scanCost (k+1) fields + 2 + completeCost (foldRuns fields []) k
    silent Record285.machine cost
      ⟨boundary,head,1+2*left,true,
        runPattern true (k+2) false (suffixBits fields retained)⟩ =
      some ⟨boundary,head+1,3+4*left,true,
        runPattern true k false (IncrementSelector.blocksBits fields (4*retained+1))⟩ := by
  dsimp only
  have hentry := enter_cycle Record285.machine boundary next scan boundary_one next_one
    k head left (suffixBits fields retained)
  have hscan := scan_shift fields k (head+2) (1+2*left) retained
  have hfinish := finish_cycle Record285.machine returnState restore boundary return_one restore_zero
    fields k head left retained
  have hh : head+2-3 = head-1 := by omega
  rw [hh] at hscan
  rw [show 4+scanCost (k+1) fields+2+completeCost (foldRuns fields []) k =
      2+((scanCost (k+1) fields+2+completeCost (foldRuns fields []) k)+2) by omega,
    silent_add,hentry]
  simp only [Option.bind_some]
  rw [silent_add,hscan]
  simp only [Option.bind_some]
  exact hfinish

/-- A blank cell behind the finite bank supplies the delimiter for the new
zero field. Cells above it remain arbitrary and are not discarded. -/
theorem suffix_append_zero (fields : List Nat) (retained : Nat) :
    IncrementSelector.blocksBits fields (4*(2*retained)+1) =
      suffixBits (fields++[0]) retained := by
  induction fields with
  | nil => simp [IncrementSelector.blocksBits,suffixBits,runPattern,bitVal]; omega
  | cons k ks ih =>
    simp only [List.cons_append,IncrementSelector.blocksBits,suffixBits,ih]

def cycleCost (fields : List Nat) (k : Nat) : Nat :=
  4+scanCost (k+1) fields+2+completeCost (foldRuns fields []) k

/-- All listed fields survive a nonfinal cycle; one reserved zero delimiter
becomes an explicit zero field. -/
theorem quotient_cycle_reserved (fields : List Nat) (k : Nat) (head : Int)
    (left retained : Nat) :
    silent Record285.machine (cycleCost fields k)
      ⟨boundary,head,1+2*left,true,
        runPattern true (k+2) false (suffixBits fields (2*retained))⟩ =
      some ⟨boundary,head+1,1+2*(1+2*left),true,
        runPattern true k false (suffixBits (fields++[0]) retained)⟩ := by
  have h := quotient_cycle fields k head left (2*retained)
  dsimp only at h
  rw [suffix_append_zero] at h
  have hl : 3+4*left = 1+2*(1+2*left) := by omega
  simpa only [cycleCost,hl] using h

def cyclesCost : Nat → Nat → List Nat → Nat
  | 0,_,_ => 0
  | n+1,remaining,fields =>
    cycleCost fields (2*n+remaining) + cyclesCost n remaining (fields++[0])

/-- Arbitrarily many successive quotient cycles, with a paid blank reserve
for each new field. The uninspected high suffix is arbitrary. -/
theorem quotient_cycles (n remaining : Nat) (fields : List Nat)
    (head : Int) (left retained : Nat) :
    silent Record285.machine (cyclesCost n remaining fields)
      ⟨boundary,head,1+2*left,true,
        runPattern true (2*n+remaining) false (suffixBits fields (2^n*retained))⟩ =
      some ⟨boundary,head+n,1+2*pushBit n true left,true,
        runPattern true remaining false (suffixBits (fields++List.replicate n 0) retained)⟩ := by
  induction n generalizing fields head left with
  | zero => simp [cyclesCost,silent,pushBit]
  | succ n ih =>
    have hpow : 2^(n+1)*retained = 2*(2^n*retained) := by
      simp only [Nat.pow_succ]
      ac_rfl
    have hlen : 2*(n+1)+remaining = (2*n+remaining)+2 := by omega
    have hfirst := quotient_cycle_reserved fields (2*n+remaining) head left (2^n*retained)
    have hrest := ih (fields++[0]) (head+1) (1+2*left)
    simp only [cyclesCost,hlen,hpow]
    rw [silent_add,hfirst]
    simp only [Option.bind_some]
    have hh : head+1+(n:Int) = head+(n+1:Nat) := by omega
    have hfields : (fields++[0])++List.replicate n 0 = fields++List.replicate (n+1) 0 := by
      simp [List.replicate_succ,List.append_assoc]
    have hl : 1+2*left = 2*left+1 := by omega
    simpa only [hh,hfields,pushBit,bitVal,if_true,hl] using hrest

/-- Physical-tape and event-accounting form of the iterated cycle theorem. -/
theorem quotient_cycles_physical (n remaining : Nat) (fields : List Nat)
    (head : Int) (left retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨boundary,head,1+2*left,true,
      runPattern true (2*n+remaining) false (suffixBits fields (2^n*retained))⟩ physical) :
    Rel ⟨boundary,head+n,1+2*pushBit n true left,true,
      runPattern true remaining false (suffixBits (fields++List.replicate n 0) retained)⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (cyclesCost n remaining fields)) ∧
    (∀ t, t < cyclesCost n remaining fields →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    (0 < n → 0 < cyclesCost n remaining fields) := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (quotient_cycles n remaining fields head left retained)
  refine ⟨hp.1,hp.2,?_⟩
  cases n with
  | zero => simp
  | succ n => simp only [cyclesCost,cycleCost]; omega

/-- The first two units initialize the quotient loop without touching the
unprocessed suffix. -/
theorem enter_boundary (M : Machine 285) (begin initial qboundary : Fin 285)
    (h1 : M.table.row begin true = ⟨true,.right,initial,false⟩)
    (h2 : M.table.row initial true = ⟨true,.right,qboundary,false⟩)
    (remaining : Nat) (head : Int) (left tail : Nat) :
    silent M 2 ⟨begin,head,left,true,runPattern true (remaining+2) false tail⟩ =
      some ⟨qboundary,head+2,1+2*(1+2*left),true,runPattern true remaining false tail⟩ := by
  simp only [silent,PhysicalNumeric.step,h1,h2,Bool.false_eq_true,if_false,bitVal,if_true,
    runPattern_succ_read,runPattern_succ_tail]
  have hh : head+1+1 = head+2 := by omega
  have hl : 2*(2*left+1)+1 = 1+2*(1+2*left) := by omega
  simp only [hh,hl]

theorem half_begin_one : Record285.machine.table.row (HalfSelector.state 0) true =
    ⟨true,.right,⟨68,by decide⟩,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem initial_one : Record285.machine.table.row (⟨68,by decide⟩ : Fin 285) true =
    ⟨true,.right,boundary,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

/-- From a clean root, perform every complete quotient cycle in the supplied
reserve. The remaining unary units, precise tape and duration are explicit;
the parity exit and return are not part of this segment. -/
theorem root_through_quotient_cycles (code : List Bool) (gap n remaining : Nat)
    (before fields : List Nat) (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let target := 2*n+remaining+2
    let left := DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail)
    let first := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
    let steps := first+2+cyclesCost n remaining fields
    silent Record285.machine steps
      (Grammar.rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields (2^n*retained))))) =
      some ⟨boundary,head+1+IncrementSelector.cost blocks+2+n,
        1+2*pushBit n true (1+2*left),true,
        runPattern true remaining false (suffixBits (fields++List.replicate n 0) retained)⟩ := by
  dsimp only
  let blocks := gap::before
  let target := 2*n+remaining+2
  let suffix := suffixBits fields (2^n*retained)
  let left := DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail)
  let first := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
  have hd := HalfDispatch.root_dispatch_half code before.length hwalk head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[target]) suffix))
  have ht := HalfDispatch.terminal_to_target code gap target before hwalk head leftTail suffix
  have ha := enter_boundary Record285.machine (HalfSelector.state 0) ⟨68,by decide⟩ boundary
    half_begin_one initial_one (2*n+remaining) (head+1+IncrementSelector.cost blocks) left suffix
  have hc := quotient_cycles n remaining fields (head+1+IncrementSelector.cost blocks+2)
    (1+2*left) retained
  have he : silent Record285.machine first
      (Grammar.rootEntry code head leftTail
        (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[target]) suffix))) =
      some ⟨HalfSelector.state 0,head+1+IncrementSelector.cost blocks,left,true,
        runPattern true target false suffix⟩ := by
    dsimp only [first]
    rw [show code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks =
      code.length+((2*gap+5)+pathCost code+IncrementSelector.cost blocks) by omega,
      silent_add,hd]
    simpa only [Option.bind_some] using ht
  rw [show first+2+cyclesCost n remaining fields = first+(2+cyclesCost n remaining fields) by omega,
    silent_add,he]
  simp only [Option.bind_some]
  rw [silent_add,ha]
  simp only [Option.bind_some]
  exact hc

theorem root_through_quotient_cycles_physical (code : List Bool) (gap n remaining : Nat)
    (before fields : List Nat) (hwalk : Grammar.walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (Grammar.rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[2*n+remaining+2])
          (suffixBits fields (2^n*retained))))) physical) :
    let blocks := gap::before
    let left := DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail)
    let steps := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks+2+
      cyclesCost n remaining fields
    Rel ⟨boundary,head+1+IncrementSelector.cost blocks+2+n,
      1+2*pushBit n true (1+2*left),true,
      runPattern true remaining false (suffixBits (fields++List.replicate n 0) retained)⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_through_quotient_cycles code gap n remaining before fields hwalk head leftTail retained)
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.HalfCycle

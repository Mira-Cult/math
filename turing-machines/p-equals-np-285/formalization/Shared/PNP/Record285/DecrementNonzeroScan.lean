import Shared.PNP.Record285.DecrementSelector
import Shared.PNP.Record285.IncrementCleanup

/-! Nonzero decrement's rightward scan up to the first double-zero delimiter.
The following leftward shift remains a separate obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroScan
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail suffixBits)

def scan : Fin 285 := ⟨46,by decide⟩
def check : Fin 285 := ⟨47,by decide⟩
def shift : Fin 285 := ⟨48,by decide⟩
def probe : Fin 285 := ⟨45,by decide⟩

structure Rows (M : Machine 285) (scan check shift : Fin 285) : Prop where
  scanOne : M.table.row scan true = ⟨true,.right,scan,false⟩
  scanZero : M.table.row scan false = ⟨false,.right,check,false⟩
  checkOne : M.table.row check true = ⟨true,.right,scan,false⟩
  checkZero : M.table.row check false = ⟨false,.left,shift,false⟩

/-- The entire left half-tape at the last field separator. -/
def scannedLeft : Nat → List Nat → Nat → Nat
  | k,[],left => pushBit k true left
  | k,next::rest,left => scannedLeft next rest (4*pushBit k true left+1)

def scanCost (k : Nat) (fields : List Nat) : Nat :=
  k+1+IncrementShift.cost fields

/-- Scan all remaining nonempty fields, stopping on the last separator
before the first double zero. The uninspected high suffix is retained. -/
theorem scan_suffix (M : Machine 285) (qscan qcheck qshift : Fin 285)
    (rows : Rows M qscan qcheck qshift) (fields : List Nat)
    (k : Nat) (head : Int) (left retained : Nat) :
    silent M (scanCost k fields)
      (atWord qscan head left (runPattern true k false (suffixBits fields retained))) =
      some (atWord qshift (head+scanCost k fields-2)
        (scannedLeft k fields left) (4*retained)) := by
  induction fields generalizing k head left with
  | nil =>
    have hs := IncrementCleanup.sweep_right M qscan true true rows.scanOne k false
      head left (suffixBits [] retained)
    have he : silent M 2
        (atWord qscan (head+k) (pushBit k true left) (2*(2*retained))) =
        some (atWord qshift (head+k) (pushBit k true left) (4*retained)) := by
      rw [show 4*retained = 2*(2*retained) by omega]
      simp only [atWord,even_bit,even_tail,silent,PhysicalNumeric.step,rows.scanZero,rows.checkZero,
        Bool.false_eq_true,if_false,bitVal,Nat.add_zero]
      have hh : head+(k:Int)+1-1 = head+(k:Int) := by omega
      rw [hh]
    simp only [scanCost,IncrementShift.cost,suffixBits,scannedLeft]
    simp only [suffixBits] at hs
    rw [show k+1+1 = k+2 by omega,silent_add,hs]
    simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    have hh : head+((k+2:Nat):Int)-2 = head+(k:Int) := by omega
    simpa only [hh] using he
  | cons next rest ih =>
    have hs := IncrementCleanup.sweep_right M qscan true true rows.scanOne k false
      head left (suffixBits (next::rest) retained)
    have he : silent M 2
        (atWord qscan (head+k) (pushBit k true left) (2*suffixBits (next::rest) retained)) =
        some (atWord qscan (head+k+2) (4*pushBit k true left+1)
          (runPattern true next false (suffixBits rest retained))) := by
      simp only [suffixBits,atWord,even_bit,even_tail,odd_bit,odd_tail,silent,
        PhysicalNumeric.step,rows.scanZero,rows.checkOne,Bool.false_eq_true,if_false,
        bitVal,if_true,Nat.add_zero]
      have hh : head+(k:Int)+1+1 = head+(k:Int)+2 := by omega
      have hl : 2*(2*pushBit k true left)+1 = 4*pushBit k true left+1 := by omega
      simp only [hh,hl]
    have hrest := ih next (head+k+2) (4*pushBit k true left+1)
    have hcost : scanCost k (next::rest) = k+(2+scanCost next rest) := by
      simp only [scanCost,IncrementShift.cost]; omega
    have hhead : head+(k:Int)+2+(scanCost next rest:Int)-2 =
      head+(scanCost k (next::rest):Int)-2 := by rw [hcost]; omega
    rw [hcost] at hhead
    rw [hcost,silent_add,hs]
    simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    rw [silent_add,he]
    simp only [Option.bind_some,scannedLeft]
    simpa only [hhead] using hrest

theorem literal_rows : Rows Record285.machine scan check shift := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem literal_scan_suffix (fields : List Nat) (k : Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (scanCost k fields)
      (atWord scan head left (runPattern true k false (suffixBits fields retained))) =
      some (atWord shift (head+scanCost k fields-2) (scannedLeft k fields left) (4*retained)) :=
  scan_suffix Record285.machine scan check shift literal_rows fields k head left retained

theorem literal_scan_suffix_physical (fields : List Nat) (k : Nat)
    (head : Int) (left retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atWord scan head left (runPattern true k false (suffixBits fields retained))) physical) :
    Rel (atWord shift (head+scanCost k fields-2) (scannedLeft k fields left) (4*retained))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (scanCost k fields)) ∧
    (∀ t, t < scanCost k fields → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < scanCost k fields := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (literal_scan_suffix fields k head left retained)
  refine ⟨hp.1,hp.2,?_⟩
  cases fields <;> simp [scanCost,IncrementShift.cost] <;> omega

structure EntryRows (M : Machine 285) (target probe scan : Fin 285) : Prop where
  targetOne : M.table.row target true = ⟨false,.right,probe,false⟩
  probeOne : M.table.row probe true = ⟨true,.right,scan,false⟩

theorem enter_nonzero (M : Machine 285) (target qprobe qscan : Fin 285)
    (rows : EntryRows M target qprobe qscan) (k : Nat) (head : Int) (left tail : Nat) :
    silent M 2 ⟨target,head,left,true,runPattern true (k+1) false tail⟩ =
      some (atWord qscan (head+2) (4*left+1) (runPattern true k false tail)) := by
  simp only [silent,PhysicalNumeric.step,rows.targetOne,rows.probeOne,
    Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero,runPattern_succ_read,runPattern_succ_tail,atWord]
  have hh : head+1+1 = head+2 := by omega
  have hl : 2*(2*left)+1 = 4*left+1 := by omega
  simp only [hh,hl]

theorem literal_entry_rows : EntryRows Record285.machine (DecrementSelector.state 0) probe scan := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- For any positive unary value, reach the leftward shift after scanning the
complete finite suffix. The scan is silent and retains the high suffix. -/
theorem target_to_shift (fields : List Nat) (k : Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (2+scanCost k fields)
      ⟨DecrementSelector.state 0,head,left,true,
        runPattern true (k+1) false (suffixBits fields retained)⟩ =
      some (atWord shift (head+scanCost k fields)
        (scannedLeft k fields (4*left+1)) (4*retained)) := by
  have he := enter_nonzero Record285.machine (DecrementSelector.state 0) probe scan
    literal_entry_rows k head left (suffixBits fields retained)
  have hs := literal_scan_suffix fields k (head+2) (4*left+1) retained
  rw [silent_add,he]
  simp only [Option.bind_some]
  have hh : head+2+(scanCost k fields:Int)-2 = head+(scanCost k fields:Int) := by omega
  simpa only [hh] using hs

theorem target_to_shift_physical (fields : List Nat) (k : Nat)
    (head : Int) (left retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨DecrementSelector.state 0,head,left,true,
      runPattern true (k+1) false (suffixBits fields retained)⟩ physical) :
    Rel (atWord shift (head+scanCost k fields)
      (scannedLeft k fields (4*left+1)) (4*retained))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (2+scanCost k fields)) ∧
    (∀ t, t < 2+scanCost k fields →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < 2+scanCost k fields := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (target_to_shift fields k head left retained)
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementNonzeroScan

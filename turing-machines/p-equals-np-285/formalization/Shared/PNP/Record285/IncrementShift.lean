import Shared.PNP.Record285.IncrementSelector

/-! Exact increment suffix-shift phase, from state 50 to state 51. The
higher tape after the first terminating zero is arbitrary and is retained. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementShift
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)

/-- A numeric word includes the cell under the head as its lowest bit. -/
def atWord (q : Fin 285) (head : Int) (left word : Nat) : PhysicalNumeric.Config 285 :=
  ⟨q,head,left,word.testBit 0,word/2⟩

/-- A suffix consists of nonempty unary blocks `1^(k+1)0`, then one zero;
`tail` is arbitrary and is not inspected beyond that zero. -/
def suffixBits : List Nat → Nat → Nat
  | [],tail => 2*tail
  | k::ks,tail => 1+2*runPattern true k false (suffixBits ks tail)

def cost : List Nat → Nat
  | [] => 1
  | k::ks => k+2+cost ks

def shiftedLeft : List Nat → Nat → Nat
  | [],left => left
  | k::ks,left => shiftedLeft ks (pushBit (k+1) true (2*left))

structure Rows (M : Machine 285) (shift scan ret : Fin 285) : Prop where
  shiftZero : M.table.row shift false = ⟨false,.left,ret,false⟩
  shiftOne : M.table.row shift true = ⟨false,.right,scan,false⟩
  scanOne : M.table.row scan true = ⟨true,.right,scan,false⟩
  scanZero : M.table.row scan false = ⟨true,.right,shift,false⟩

@[simp] theorem even_bit (n : Nat) : (2*n).testBit 0 = false := by
  simp [Nat.testBit_zero]

@[simp] theorem even_tail (n : Nat) : (2*n)/2 = n := by omega

/-- Scan zero or more ones, replace the next zero with one, and continue in
shift state. The suffix after that zero is untouched. -/
theorem scan_to_zero (M : Machine 285) (shift scan ret : Fin 285)
    (rows : Rows M shift scan ret) (k : Nat) (head : Int) (left suffix : Nat) :
    silent M (k+1) (atWord scan head left (runPattern true k false suffix)) =
      some (atWord shift (head+(k+1)) (pushBit (k+1) true left) suffix) := by
  cases k with
  | zero =>
    simp only [runPattern, bitVal, if_false, Nat.zero_add,
      atWord, even_bit, even_tail, silent, PhysicalNumeric.step, rows.scanZero,
      Bool.false_eq_true, if_false, pushBit, if_true, Int.natCast_zero, Int.zero_add]
  | succ k =>
    have hscan := run_sweep_right M scan true true rows.scanOne k false suffix left head
    have hlast : silent M 1 ⟨scan,head+(k+1),pushBit (k+1) true left,false,suffix⟩ =
        some (atWord shift (head+(k+1)+1) (2*pushBit (k+1) true left+1) suffix) := by
      simp only [silent, PhysicalNumeric.step, rows.scanZero, Bool.false_eq_true, if_false,
        bitVal, if_true, atWord]
    have hstart : atWord scan head left (runPattern true (k+1) false suffix) =
        ⟨scan,head,left,true,runPattern true k false suffix⟩ := by
      simp only [runPattern, bitVal, if_true, odd_bit, odd_tail, atWord]
    rw [hstart, show (k+1)+1 = (k+1)+1 by rfl, silent_add, hscan]
    simp only [Option.bind_some]
    have hp : pushBit ((k+1)+1) true left = 2*pushBit (k+1) true left+1 := by
      rw [pushBit, pushBit_affine]
      rfl
    rw [hp]
    simpa only [Int.natCast_succ, Int.add_assoc] using hlast

/-- Move one nonempty suffix field across the shifting gap. -/
theorem shift_block (M : Machine 285) (shift scan ret : Fin 285)
    (rows : Rows M shift scan ret) (k : Nat) (head : Int) (left suffix : Nat) :
    silent M (k+2) (atWord shift head left (1+2*runPattern true k false suffix)) =
      some (atWord shift (head+(k+2)) (pushBit (k+1) true (2*left)) suffix) := by
  have hfirst : silent M 1
      (atWord shift head left (1+2*runPattern true k false suffix)) =
      some (atWord scan (head+1) (2*left) (runPattern true k false suffix)) := by
    simp only [atWord, odd_bit, odd_tail, silent, PhysicalNumeric.step, rows.shiftOne,
      Bool.false_eq_true, if_false, bitVal, if_false, Nat.add_zero]
  have hrest := scan_to_zero M shift scan ret rows k (head+1) (2*left) suffix
  rw [show k+2 = 1+(k+1) by omega, silent_add, hfirst]
  simp only [Option.bind_some]
  have hh : (head+1)+(k+1) = head+((k+2:Nat):Int) := by omega
  simpa only [hh, Int.natCast_add, show ((2:Nat):Int) = 2 by rfl] using hrest

/-- The complete finite suffix shift reaches the return scanner, preserving
all high suffix bits past the terminating zero and emitting no event. -/
theorem shift_suffix (M : Machine 285) (shift scan ret : Fin 285)
    (rows : Rows M shift scan ret) (blocks : List Nat) (head : Int) (left tail : Nat) :
    silent M (cost blocks) (atWord shift head left (suffixBits blocks tail)) =
      some ⟨ret,head+cost blocks-2,(shiftedLeft blocks left)/2,
        (shiftedLeft blocks left).testBit 0,2*tail⟩ := by
  induction blocks generalizing head left with
  | nil =>
    simp only [cost,suffixBits,shiftedLeft,atWord,even_bit,even_tail,silent,
      PhysicalNumeric.step,rows.shiftZero,Bool.false_eq_true,if_false,bitVal,if_false,
      Nat.add_zero,Int.natCast_one]
    have he : head-1 = head+1-2 := by omega
    rw [he]
  | cons k ks ih =>
    have hblock := shift_block M shift scan ret rows k head left (suffixBits ks tail)
    have hrest := ih (head+(k+2)) (pushBit (k+1) true (2*left))
    simp only [cost,suffixBits,shiftedLeft]
    rw [silent_add, hblock]
    simp only [Option.bind_some]
    have hh : head+(k+2)+(cost ks:Int)-2 = head+((k+2+cost ks:Nat):Int)-2 := by omega
    simpa only [Int.natCast_add, hh] using hrest

def scanState : Fin 285 := ⟨14,by decide⟩
def returnState : Fin 285 := ⟨51,by decide⟩

/-- The four literal rows implementing the suffix-shift loop. -/
theorem literal_rows : Rows Record285.machine IncrementSelector.shiftState scanState returnState := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- Literal suffix shift for arbitrary finite unary fields and arbitrary
retained high suffix, including an empty list of fields. -/
theorem literal_shift (blocks : List Nat) (head : Int) (left tail : Nat) :
    silent Record285.machine (cost blocks)
      (atWord IncrementSelector.shiftState head left (suffixBits blocks tail)) =
      some ⟨returnState,head+cost blocks-2,(shiftedLeft blocks left)/2,
        (shiftedLeft blocks left).testBit 0,2*tail⟩ :=
  shift_suffix Record285.machine IncrementSelector.shiftState scanState returnState
    literal_rows blocks head left tail

theorem cost_positive (blocks : List Nat) : 0 < cost blocks := by
  cases blocks <;> simp [cost] <;> omega

/-- Full integer-tape version of the suffix-shift contract. -/
theorem literal_shift_physical (blocks : List Nat) (head : Int) (left tail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atWord IncrementSelector.shiftState head left (suffixBits blocks tail)) physical) :
    Rel ⟨returnState,head+cost blocks-2,(shiftedLeft blocks left)/2,
        (shiftedLeft blocks left).testBit 0,2*tail⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (cost blocks)) ∧
    ∀ t, t < cost blocks →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_shift blocks head left tail)

/-- The actual selector and the complete suffix shift compose into one finite,
silent physical segment, preserving an arbitrary high suffix after the first
two-zero boundary. The later return scanner is not included. -/
theorem selector_and_shift (selected suffix : List Nat) (hbound : selected.length ≤ 16)
    (head : Int) (left retained : Nat) :
    silent Record285.machine (IncrementSelector.cost selected + cost suffix)
      ⟨IncrementSelector.literalState selected.length,head,left,false,
        IncrementSelector.blocksBits selected (suffixBits suffix retained)⟩ =
      some ⟨returnState,head+IncrementSelector.cost selected+cost suffix-2,
        (shiftedLeft suffix (IncrementSelector.leftAfter selected left))/2,
        (shiftedLeft suffix (IncrementSelector.leftAfter selected left)).testBit 0,2*retained⟩ := by
  have hselect := IncrementSelector.literal_select selected hbound head left (suffixBits suffix retained)
  have hshift := literal_shift suffix (head+IncrementSelector.cost selected)
    (IncrementSelector.leftAfter selected left) retained
  rw [silent_add, hselect]
  simp only [Option.bind_some]
  exact hshift

/-- The composed selector and shift on the entire physical tape. -/
theorem selector_and_shift_physical (selected suffix : List Nat) (hbound : selected.length ≤ 16)
    (head : Int) (left retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState selected.length,head,left,false,
      IncrementSelector.blocksBits selected (suffixBits suffix retained)⟩ physical) :
    Rel ⟨returnState,head+IncrementSelector.cost selected+cost suffix-2,
        (shiftedLeft suffix (IncrementSelector.leftAfter selected left))/2,
        (shiftedLeft suffix (IncrementSelector.leftAfter selected left)).testBit 0,2*retained⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run
        (IncrementSelector.cost selected + cost suffix)) ∧
    ∀ t, t < IncrementSelector.cost selected + cost suffix →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (selector_and_shift selected suffix hbound head left retained)

end Shared.PNP.Record285.IncrementShift

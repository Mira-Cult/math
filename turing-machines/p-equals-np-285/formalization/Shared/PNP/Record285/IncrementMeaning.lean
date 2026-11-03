import Shared.PNP.Record285.IncrementReturn

/-! Exact unary-bank meaning of the literal increment segment. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementMeaning
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementReturn

/-- Record preceding fields in the order in which the return scanner sees them. -/
def foldRuns : List Nat → List Nat → List Nat
  | [], runs => runs
  | k::ks, runs => foldRuns ks (k::runs)

/-- Reconstruct the fields behind the return scanner. -/
def backFold : List Nat → Nat → Nat
  | [], right => right
  | k::ks, right => backFold ks (2*pushBit (k+1) true right)

/-- One encoded nonempty unary field followed by its zero. -/
theorem blocks_cons (k : Nat) (ks : List Nat) (tail : Nat) :
    IncrementSelector.blocksBits (k::ks) tail =
      pushBit (k+1) true (2*IncrementSelector.blocksBits ks tail) := by
  rw [push_run]
  simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true]

theorem blocks_append (xs ys : List Nat) (tail : Nat) :
    IncrementSelector.blocksBits (xs++ys) tail =
      IncrementSelector.blocksBits xs (IncrementSelector.blocksBits ys tail) := by
  induction xs with
  | nil => rfl
  | cons k ks ih => simp only [List.cons_append,blocks_cons,ih]

theorem backFold_foldRuns (xs runs : List Nat) (tail : Nat) :
    backFold (foldRuns xs runs) (2*tail) =
      backFold runs (2*IncrementSelector.blocksBits xs tail) := by
  induction xs generalizing runs with
  | nil => rfl
  | cons k ks ih =>
    simp only [foldRuns,ih,backFold,blocks_cons]

theorem scan_output (runs : List Nat) (last right : Nat) :
    completeRight runs last (2*right+1) =
      4*pushBit (last+1) true (backFold runs right) := by
  induction runs generalizing right with
  | nil =>
    simp only [completeRight,backFold,pushBit,bitVal,if_true]
  | cons k ks ih =>
    simp only [completeRight,backFold]
    have hp : pushBit k true (2*right+1) = pushBit (k+1) true right := by
      rw [pushBit]
      rfl
    rw [hp, show 4*pushBit (k+1) true right+1 =
      2*(2*pushBit (k+1) true right)+1 by omega, ih]

/-- The source output from scanning a leading one, then a complete return word. -/
theorem scan_leading (M : Machine 285) (scan check next : Fin 285)
    (rows : Rows M scan check next) (runs : List Nat) (last : Nat)
    (head : Int) (farLeft right : Nat) :
    silent M (1+completeCost runs last)
      (atLeftWord scan head (1+2*completeBits runs last farLeft) right) =
      some (atLeftWord next (head-(1+completeCost runs last)) farLeft
        (completeRight runs last (2*right+1))) := by
  have hfirst : silent M 1
      (atLeftWord scan head (1+2*completeBits runs last farLeft) right) =
      some (atLeftWord scan (head-1) (completeBits runs last farLeft) (2*right+1)) := by
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.scanOne,
      Bool.false_eq_true,if_false,bitVal,if_true]
  have hrest := scan_complete M scan check next rows runs last (head-1) farLeft (2*right+1)
  rw [silent_add,hfirst]
  simp only [Option.bind_some]
  have hh : head-1-(completeCost runs last:Int) = head-((1+completeCost runs last:Nat):Int) := by omega
  simpa only [Int.natCast_add,Int.natCast_one,hh] using hrest

/-- Selection through fields before the selected field, then increment it. -/
theorem leftAfter_selected (before runs : List Nat) (target last farLeft : Nat) :
    IncrementSelector.leftAfter (before++[target]) (1+2*completeBits runs last farLeft) =
      1+2*completeBits ((target+1)::foldRuns before runs) last farLeft := by
  induction before generalizing runs with
  | nil =>
    simp only [List.nil_append,IncrementSelector.leftAfter,push_field_layout,foldRuns,
      completeBits,runPattern,bitVal,if_true]
    omega
  | cons k ks ih =>
    simp only [List.cons_append,IncrementSelector.leftAfter,push_field_layout,foldRuns]
    exact ih (k::runs)

theorem shiftedLeft_fields (suffix runs : List Nat) (last farLeft : Nat) :
    IncrementShift.shiftedLeft suffix (1+2*completeBits runs last farLeft) =
      1+2*completeBits (foldRuns suffix runs) last farLeft := by
  induction suffix generalizing runs with
  | nil => rfl
  | cons k ks ih =>
    simp only [IncrementShift.shiftedLeft,push_field_layout,foldRuns]
    exact ih (k::runs)

/-- The entire shifted left word has a calculable scanner representation. -/
theorem exact_return_layout (gap target : Nat) (before suffix : List Nat) (farLeft : Nat) :
    IncrementShift.shiftedLeft suffix
      (IncrementSelector.leftAfter (gap::(before++[target])) (2*farLeft)) =
      1+2*completeBits (foldRuns suffix ((target+1)::foldRuns before [])) gap farLeft := by
  have hfirst : pushBit (gap+1) true (2*(2*farLeft)) =
      1+2*completeBits [] gap farLeft := by
    rw [push_run]
    simp only [runPattern,completeBits,bitVal,if_true]
  simp only [IncrementSelector.leftAfter,hfirst,leftAfter_selected,shiftedLeft_fields]

/-- Returning reconstructs exactly the bank with the selected field increased. -/
theorem exact_return_output (gap target : Nat) (before suffix : List Nat) (retained : Nat) :
    completeRight (foldRuns suffix ((target+1)::foldRuns before [])) gap (2*(2*retained)+1) =
      4*IncrementSelector.blocksBits (gap::(before++[target+1]))
        (IncrementSelector.blocksBits suffix retained) := by
  rw [scan_output, backFold_foldRuns]
  simp only [backFold, ← blocks_cons, ← blocks_append]
  rw [backFold_foldRuns]
  simp only [backFold, ← blocks_cons, ← blocks_append]
  congr 2
  simp [List.append_assoc]

/-- The total length of the nonempty unary fields including separators. -/
def fieldCost : List Nat → Nat
  | [] => 0
  | k::ks => k+2+fieldCost ks

theorem selector_cost (xs : List Nat) : IncrementSelector.cost xs = fieldCost xs+1 := by
  induction xs with
  | nil => rfl
  | cons k ks ih => simp only [IncrementSelector.cost,fieldCost,ih]; omega

theorem shift_cost (xs : List Nat) : IncrementShift.cost xs = fieldCost xs+1 := by
  induction xs with
  | nil => rfl
  | cons k ks ih => simp only [IncrementShift.cost,fieldCost,ih]; omega

theorem fieldCost_append (xs ys : List Nat) : fieldCost (xs++ys) = fieldCost xs+fieldCost ys := by
  induction xs with
  | nil => simp [fieldCost]
  | cons k ks ih => simp only [List.cons_append,fieldCost,ih]; omega

theorem folded_cost (xs runs : List Nat) (last : Nat) :
    completeCost (foldRuns xs runs) last = completeCost runs last+fieldCost xs := by
  induction xs generalizing runs with
  | nil => simp [foldRuns,fieldCost]
  | cons k ks ih => simp only [foldRuns,ih,completeCost,fieldCost]; omega

/-- The return scanner travels exactly back to the cell left of the two-zero
boundary, irrespective of field values or the number of suffix fields. -/
theorem return_distance (gap target : Nat) (before suffix : List Nat) :
    1+completeCost (foldRuns suffix ((target+1)::foldRuns before [])) gap =
      IncrementSelector.cost (gap::(before++[target]))+IncrementShift.cost suffix := by
  simp only [folded_cost,completeCost,selector_cost,shift_cost,fieldCost,
    fieldCost_append]
  omega

/-- Exact numeric execution of the literal selector, shift, and return. The
bank encoding uses low-bit-first nonempty runs; only the selected parameter
is increased by one, and the retained high tape is unchanged as data. -/
theorem literal_increment (gap target : Nat) (before suffix : List Nat)
    (hbound : (gap::(before++[target])).length ≤ 16)
    (head : Int) (retained farLeft : Nat) :
    let selected := gap::(before++[target])
    let steps := 2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    silent Record285.machine steps
      ⟨IncrementSelector.literalState selected.length,head,2*farLeft,false,
        IncrementSelector.blocksBits selected (IncrementShift.suffixBits suffix retained)⟩ =
      some (atLeftWord breakState (head-2) farLeft
        (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
          (IncrementSelector.blocksBits suffix retained))) := by
  dsimp only
  let selected := gap::(before++[target])
  let runs := foldRuns suffix ((target+1)::foldRuns before [])
  let n := IncrementSelector.cost selected+IncrementShift.cost suffix
  have hs := IncrementShift.selector_and_shift selected suffix hbound head (2*farLeft) retained
  have hl := exact_return_layout gap target before suffix farLeft
  have hr := scan_leading Record285.machine IncrementShift.returnState checkState breakState
    literal_rows runs gap (head+n-2) farLeft (2*retained)
  have hd : 1+completeCost runs gap = n := return_distance gap target before suffix
  have ho := exact_return_output gap target before suffix retained
  rw [show 2*n = n+n by omega, silent_add, hs]
  simp only [Option.bind_some]
  rw [← hd]
  change IncrementShift.shiftedLeft suffix (IncrementSelector.leftAfter selected (2*farLeft)) =
    1+2*completeBits runs gap farLeft at hl
  change completeRight runs gap (2*(2*retained)+1) =
    4*IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained) at ho
  have hh : head+(n:Int)-2-(1+(completeCost runs gap:Int)) = head-2 := by omega
  have hh2 : head+(n:Int)-2 =
      head+(IncrementSelector.cost selected:Int)+(IncrementShift.cost suffix:Int)-2 := by
    dsimp [n]
    omega
  simp only [atLeftWord] at hr
  rw [← hl, ho, hh, hh2] at hr
  simpa only [atLeftWord] using hr

/-- The extra zero after the finite suffix is the cell consumed by increment. -/
theorem suffix_bits (suffix : List Nat) (retained : Nat) :
    IncrementShift.suffixBits suffix retained =
      IncrementSelector.blocksBits suffix (2*retained) := by
  induction suffix with
  | nil => rfl
  | cons k ks ih => simp only [IncrementShift.suffixBits,IncrementSelector.blocksBits,ih]

/-- The added unary one and the consumed boundary zero cancel in length, so
the arbitrary retained suffix starts at the same absolute tape position. -/
theorem retained_offset (gap target : Nat) (before suffix : List Nat) :
    fieldCost (gap::(before++[target]))+fieldCost suffix+1 =
      fieldCost (gap::(before++[target+1]))+fieldCost suffix := by
  simp only [fieldCost,fieldCost_append]
  omega

/-- Removing the encoded run and separator recovers every later bit. -/
theorem run_extract (k tail : Nat) : runPattern true k false tail / 2^(k+1) = tail := by
  induction k with
  | zero => simp [runPattern,bitVal]
  | succ k ih =>
    rw [show (k+1)+1 = (k+1)+1 by rfl, Nat.pow_succ, Nat.mul_comm,
      ← Nat.div_div_eq_div_mul, runPattern]
    simp only [bitVal,if_true,odd_tail]
    exact ih

theorem blocks_extract (xs : List Nat) (tail : Nat) :
    IncrementSelector.blocksBits xs tail / 2^(fieldCost xs) = tail := by
  induction xs with
  | nil => simp [IncrementSelector.blocksBits,fieldCost]
  | cons k ks ih =>
    rw [fieldCost, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    have hfield : IncrementSelector.blocksBits (k::ks) tail =
        runPattern true (k+1) false (IncrementSelector.blocksBits ks tail) := by
      simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true]
    rw [hfield, show k+2 = (k+1)+1 by omega, run_extract,ih]

/-- Both encoded words recover the same retained tail at the same bit offset. -/
theorem retained_tail_exact (gap target : Nat) (before suffix : List Nat) (retained : Nat) :
    let input := IncrementSelector.blocksBits (gap::(before++[target]))
      (IncrementShift.suffixBits suffix retained)
    let output := IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained)
    let offset := fieldCost (gap::(before++[target]))+fieldCost suffix+1
    input / 2^offset = retained ∧ output / 2^offset = retained := by
  dsimp only
  constructor
  · rw [suffix_bits, ← blocks_append, ← fieldCost_append,
      Nat.pow_succ, ← Nat.div_div_eq_div_mul, blocks_extract]
    omega
  · rw [retained_offset, ← blocks_append, ← fieldCost_append, blocks_extract]

/-- Equality of every bit in the retained high suffix, at its original offset. -/
theorem retained_bit_exact (gap target : Nat) (before suffix : List Nat) (retained bit : Nat) :
    let input := IncrementSelector.blocksBits (gap::(before++[target]))
      (IncrementShift.suffixBits suffix retained)
    let output := IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained)
    let offset := fieldCost (gap::(before++[target]))+fieldCost suffix+1
    input.testBit (bit+offset) = output.testBit (bit+offset) := by
  have h := retained_tail_exact gap target before suffix retained
  dsimp only at h ⊢
  rw [← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow, h.1, h.2]

/-- The head moves two cells left; the retained suffix nevertheless stays at
its original absolute tape positions. -/
theorem retained_physical_offset (gap target : Nat) (before suffix : List Nat) (retained bit : Nat) :
    let input := IncrementSelector.blocksBits (gap::(before++[target]))
      (IncrementShift.suffixBits suffix retained)
    let output := IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained)
    let offset := fieldCost (gap::(before++[target]))+fieldCost suffix+1
    (4*output).testBit ((bit+offset)+2) = input.testBit (bit+offset) := by
  dsimp only
  let output := IncrementSelector.blocksBits (gap::(before++[target+1]))
    (IncrementSelector.blocksBits suffix retained)
  let offset := fieldCost (gap::(before++[target]))+fieldCost suffix+1
  calc
    (4*output).testBit ((bit+offset)+2) = ((4*output)/2^2).testBit (bit+offset) :=
      (Nat.testBit_div_two_pow (n:=2) (4*output) (bit+offset)).symm
    _ = output.testBit (bit+offset) := by
      have h : (4*output)/2^2 = output := by omega
      rw [h]
    _ = _ := (retained_bit_exact gap target before suffix retained bit).symm

theorem literal_increment_steps_positive (gap target : Nat) (before suffix : List Nat) :
    0 < 2*(IncrementSelector.cost (gap::(before++[target]))+IncrementShift.cost suffix) := by
  have h := IncrementSelector.cost_positive (gap::(before++[target]))
  omega

/-- The same exact increment on the full physical tape, with no marked events. -/
theorem literal_increment_physical (gap target : Nat) (before suffix : List Nat)
    (hbound : (gap::(before++[target])).length ≤ 16)
    (head : Int) (retained farLeft : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState (gap::(before++[target])).length,
      head,2*farLeft,false,IncrementSelector.blocksBits (gap::(before++[target]))
        (IncrementShift.suffixBits suffix retained)⟩ physical) :
    let selected := gap::(before++[target])
    let steps := 2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    Rel (atLeftWord breakState (head-2) farLeft
      (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
        (IncrementSelector.blocksBits suffix retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  exact silent_physical Record285.machine _ physical hrel _ _
    (literal_increment gap target before suffix hbound head retained farLeft)

/-- All cells in the retained suffix have exactly the same absolute tape
positions and values before and after the physical increment. -/
theorem literal_increment_retained_cells (gap target : Nat) (before suffix : List Nat)
    (hbound : (gap::(before++[target])).length ≤ 16)
    (head : Int) (retained farLeft : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState (gap::(before++[target])).length,
      head,2*farLeft,false,IncrementSelector.blocksBits (gap::(before++[target]))
        (IncrementShift.suffixBits suffix retained)⟩ physical) :
    let selected := gap::(before++[target])
    let steps := 2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    let offset := fieldCost selected+fieldCost suffix+1
    ∀ bit : Nat,
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps).tape
        (head+(bit+offset:Int)+1) = physical.tape (head+(bit+offset:Int)+1) := by
  dsimp only
  let offset := fieldCost (gap::(before++[target]))+fieldCost suffix+1
  have hrun := (literal_increment_physical gap target before suffix hbound head retained farLeft physical hrel).1
  intro bit
  have hi := hrel.2.2.2.2 (bit+offset)
  have ho := hrun.2.2.2.2 ((bit+offset)+2)
  simp only [Shared.PNP.Record285.RelativeTape.aheadPos, Bool.false_eq_true, if_false] at hi ho
  rw [← hrel.2.1] at hi
  rw [← hrun.2.1] at ho
  dsimp only [atLeftWord] at ho
  dsimp only at hi
  simp only [Int.natCast_add, show ((2:Nat):Int) = 2 by rfl] at hi ho ⊢
  have hpos : head-2+((bit+offset)+2:Int)+1 = head+(bit+offset:Int)+1 := by omega
  rw [hpos] at ho
  have hb := retained_physical_offset gap target before suffix retained bit
  exact ho.trans (hb.trans hi.symm)

/-- The full tape at and to the left of the break position is also preserved. -/
theorem literal_increment_left_cells (gap target : Nat) (before suffix : List Nat)
    (hbound : (gap::(before++[target])).length ≤ 16)
    (head : Int) (retained farLeft : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState (gap::(before++[target])).length,
      head,2*farLeft,false,IncrementSelector.blocksBits (gap::(before++[target]))
        (IncrementShift.suffixBits suffix retained)⟩ physical) :
    let selected := gap::(before++[target])
    let steps := 2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    ∀ bit : Nat,
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps).tape
        (head-2-bit) = physical.tape (head-2-bit) := by
  dsimp only
  have hrun := (literal_increment_physical gap target before suffix hbound head retained farLeft physical hrel).1
  intro bit
  have hi := hrel.2.2.2.1 (bit+1)
  simp only [Shared.PNP.Record285.RelativeTape.behindPos, Bool.false_eq_true, if_false] at hi
  rw [← hrel.2.1] at hi
  dsimp only at hi
  have hshift : (2*farLeft).testBit (bit+1) = farLeft.testBit bit := by
    calc
      (2*farLeft).testBit (bit+1) = ((2*farLeft)/2^1).testBit bit :=
        (Nat.testBit_div_two_pow (n:=1) (2*farLeft) bit).symm
      _ = farLeft.testBit bit := by
        have h : (2*farLeft)/2^1 = farLeft := by omega
        exact congrArg (fun x => x.testBit bit) h
  rw [hshift] at hi
  have hpos : head-((bit+1:Nat):Int)-1 = head-2-(bit:Int) := by omega
  rw [hpos] at hi
  cases bit with
  | zero =>
    have ho := hrun.2.2.1
    rw [← hrun.2.1] at ho
    dsimp only [atLeftWord] at ho
    simpa only [Int.natCast_zero, Int.sub_zero] using ho.trans hi.symm
  | succ bit =>
    have ho := hrun.2.2.2.1 bit
    simp only [Shared.PNP.Record285.RelativeTape.behindPos, Bool.false_eq_true, if_false] at ho
    rw [← hrun.2.1] at ho
    dsimp only [atLeftWord] at ho
    have hp : head-2-(bit:Int)-1 = head-2-((bit+1:Nat):Int) := by omega
    rw [hp, Nat.testBit_div_two_pow (n:=1)] at ho
    exact ho.trans hi.symm

/-- Field indices 0 through 14: `before.length` is the selected physical
index, and the selector state is exactly the emitted index-specific state. -/
theorem literal_increment_field_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (head : Int) (retained farLeft : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState (before.length+2),head,2*farLeft,false,
      IncrementSelector.blocksBits (gap::(before++[target]))
        (IncrementShift.suffixBits suffix retained)⟩ physical) :
    let selected := gap::(before++[target])
    let steps := 2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    Rel (atLeftWord breakState (head-2) farLeft
      (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
        (IncrementSelector.blocksBits suffix retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  have hlen : (gap::(before++[target])).length = before.length+2 := by simp
  have hbound : (gap::(before++[target])).length ≤ 16 := by omega
  have hrel' : Rel ⟨IncrementSelector.literalState (gap::(before++[target])).length,
      head,2*farLeft,false,IncrementSelector.blocksBits (gap::(before++[target]))
        (IncrementShift.suffixBits suffix retained)⟩ physical := by
    simpa only [hlen] using hrel
  exact literal_increment_physical gap target before suffix hbound head retained farLeft physical hrel'

end Shared.PNP.Record285.IncrementMeaning

import Shared.PNP.Record285.IncrementShift

/-! Exact leftward return scanner for ordinary increment. A finite list of
run lengths specifies the cells up to the first `00`; an arbitrary high prefix
beyond that boundary is preserved. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementReturn
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail)

/-- A low-bit-first word includes the head and continues to the left. -/
def atLeftWord (q : Fin 285) (head : Int) (word right : Nat) : PhysicalNumeric.Config 285 :=
  ⟨q,head,word/2,word.testBit 0,right⟩

/-- A run of `k` ones, then `01`, repeated until the terminal `00`.
`retained` contains all cells strictly to the left of that terminal. -/
def returnBits : List Nat → Nat → Nat
  | [],retained => 4*retained
  | k::ks,retained => runPattern true k false (1+2*returnBits ks retained)

def cost : List Nat → Nat
  | [] => 2
  | k::ks => k+2+cost ks

def returnedRight : List Nat → Nat → Nat
  | [],right => 4*right
  | k::ks,right => returnedRight ks (4*pushBit k true right+1)

structure Rows (M : Machine 285) (scan check next : Fin 285) : Prop where
  scanOne : M.table.row scan true = ⟨true,.left,scan,false⟩
  scanZero : M.table.row scan false = ⟨false,.left,check,false⟩
  checkOne : M.table.row check true = ⟨true,.left,scan,false⟩
  checkZero : M.table.row check false = ⟨false,.left,next,false⟩

/-- Scan a run of `k` ones and the following `01`, returning to scan state. -/
theorem return_block (M : Machine 285) (scan check next : Fin 285)
    (rows : Rows M scan check next) (k : Nat) (head : Int) (word right : Nat) :
    silent M (k+2) (atLeftWord scan head (runPattern true k false (1+2*word)) right) =
      some (atLeftWord scan (head-(k+2)) word (4*pushBit k true right+1)) := by
  cases k with
  | zero =>
    simp only [runPattern, bitVal, if_false, Nat.zero_add, atLeftWord, pushBit,
      silent, PhysicalNumeric.step, rows.scanZero, rows.checkOne, even_tail, even_bit,
      odd_bit, odd_tail, Bool.false_eq_true, if_false, if_true]
    have hh : head - 1 - 1 = head - 2 := by omega
    have hr : 2 * (2 * right + 0) + 1 = 4 * right + 1 := by omega
    simp only [Int.natCast_zero, Int.zero_add, hh, hr]
  | succ k =>
    have hscan := run_sweep_left M scan true true rows.scanOne k false (1+2*word) right head
    have hpair := pair_left M scan check false false true rows.scanZero rows.checkOne
      (head-(k+1)) (1+2*word) (pushBit (k+1) true right) (odd_bit word)
    have hfirst : atLeftWord scan head (runPattern true (k+1) false (1+2*word)) right =
        ⟨scan,head,runPattern true k false (1+2*word),true,right⟩ := by
      simp only [atLeftWord,runPattern,bitVal,if_true,odd_bit,odd_tail]
    rw [hfirst, show (k+1)+2 = (k+1)+2 by rfl, silent_add, hscan]
    simp only [Option.bind_some]
    have he : (1+2*word)/4 = word/2 := by omega
    have hb : ((1+2*word)/2).testBit 0 = word.testBit 0 := by rw [odd_tail]
    simp only [he,hb,bitVal,Bool.false_eq_true,if_false,if_true,Nat.mul_zero,Nat.add_zero] at hpair
    have hh2 : head - ((k:Int) + 1 + ((2:Nat):Int)) = head - ((k:Int) + 1 + 2) := by omega
    have hh3 : head - ((k:Int) + 1) - 2 = head - ((k:Int) + 1 + 2) := by omega
    simpa only [atLeftWord,Int.natCast_add,Int.natCast_one,hh2,hh3] using hpair

/-- Full scanner contract: exact positive time, all data on both sides,
and no events, for any finite runs and arbitrary retained high prefix. -/
theorem scan_return (M : Machine 285) (scan check next : Fin 285)
    (rows : Rows M scan check next) (runs : List Nat) (head : Int) (retained right : Nat) :
    silent M (cost runs) (atLeftWord scan head (returnBits runs retained) right) =
      some (atLeftWord next (head-cost runs) retained (returnedRight runs right)) := by
  induction runs generalizing head right with
  | nil =>
    simp only [cost,returnBits,returnedRight,atLeftWord,silent,PhysicalNumeric.step]
    have h0 : (4*retained).testBit 0 = false := by
      rw [show 4*retained = 2*(2*retained) by omega, even_bit]
    have h1 : (4*retained)/2 = 2*retained := by omega
    simp only [h0,h1,rows.scanZero,Bool.false_eq_true,if_false,bitVal,if_false,Nat.add_zero,
      IncrementShift.even_bit, IncrementShift.even_tail,rows.checkZero]
    have hh : head - 1 - 1 = head - 2 := by omega
    have hr : 2 * (2 * right) = 4 * right := by omega
    simp only [show ((2:Nat):Int) = 2 by rfl, hh, hr]
  | cons k ks ih =>
    have hblock := return_block M scan check next rows k head (returnBits ks retained) right
    have hrest := ih (head-(k+2)) (4*pushBit k true right+1)
    simp only [cost,returnBits,returnedRight]
    rw [silent_add, hblock]
    simp only [Option.bind_some]
    have hh : head-(k+2)-(cost ks:Int) = head-((k+2+cost ks:Nat):Int) := by omega
    simpa only [Int.natCast_add,hh] using hrest


/-- General form: after the `01` cycles, the terminal `00` may be
preceded by any finite final run of ones. -/
def completeBits : List Nat → Nat → Nat → Nat
  | [],last,retained => runPattern true last false (2*retained)
  | k::ks,last,retained => runPattern true k false (1+2*completeBits ks last retained)

def completeCost : List Nat → Nat → Nat
  | [],last => last+2
  | k::ks,last => k+2+completeCost ks last

def completeRight : List Nat → Nat → Nat → Nat
  | [],last,right => 4*pushBit last true right
  | k::ks,last,right => completeRight ks last (4*pushBit k true right+1)

theorem scan_final (M : Machine 285) (scan check next : Fin 285)
    (rows : Rows M scan check next) (last : Nat) (head : Int) (retained right : Nat) :
    silent M (last+2) (atLeftWord scan head (runPattern true last false (2*retained)) right) =
      some (atLeftWord next (head-(last+2)) retained (4*pushBit last true right)) := by
  cases last with
  | zero =>
    have h := scan_return M scan check next rows [] head retained right
    have hh : head - ((2:Nat):Int) = head - 2 := by omega
    simpa only [hh,runPattern,bitVal,if_false,Nat.zero_add,returnBits,cost,returnedRight,
      pushBit,Bool.false_eq_true,if_false,Nat.zero_add,Int.natCast_zero,Int.zero_add,
      show 2*(2*retained) = 4*retained by omega] using h
  | succ k =>
    have hscan := run_sweep_left M scan true true rows.scanOne k false (2*retained) right head
    have hrest := scan_return M scan check next rows [] (head-(k+1)) retained
      (pushBit (k+1) true right)
    have hfirst : atLeftWord scan head (runPattern true (k+1) false (2*retained)) right =
        ⟨scan,head,runPattern true k false (2*retained),true,right⟩ := by
      simp only [atLeftWord,runPattern,bitVal,if_true,odd_bit,odd_tail]
    rw [hfirst,silent_add,hscan]
    simp only [Option.bind_some]
    have hh : head-(k+1)-2 = head-((k+1)+2:Nat) := by omega
    simpa only [returnBits,cost,returnedRight,atLeftWord,Int.natCast_add,Int.natCast_one,
      show ((2:Nat):Int) = 2 by rfl,hh,
      show 4*retained/2 = 2*retained by omega,
      show (4*retained).testBit 0 = false by rw [show 4*retained = 2*(2*retained) by omega, even_bit]] using hrest

theorem scan_complete (M : Machine 285) (scan check next : Fin 285)
    (rows : Rows M scan check next) (runs : List Nat) (last : Nat) (head : Int)
    (retained right : Nat) :
    silent M (completeCost runs last) (atLeftWord scan head (completeBits runs last retained) right) =
      some (atLeftWord next (head-completeCost runs last) retained (completeRight runs last right)) := by
  induction runs generalizing head right with
  | nil => exact scan_final M scan check next rows last head retained right
  | cons k ks ih =>
    have hblock := return_block M scan check next rows k head (completeBits ks last retained) right
    have hrest := ih (head-(k+2)) (4*pushBit k true right+1)
    simp only [completeBits,completeCost,completeRight]
    rw [silent_add,hblock]
    simp only [Option.bind_some]
    have hh : head-(k+2)-(completeCost ks last:Int) =
      head-((k+2+completeCost ks last:Nat):Int) := by omega
    simpa only [Int.natCast_add,hh] using hrest

def checkState : Fin 285 := ⟨52,by decide⟩
def breakState : Fin 285 := ⟨1,by decide⟩

theorem literal_rows : Rows Record285.machine IncrementShift.returnState checkState breakState := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem literal_return (runs : List Nat) (head : Int) (retained right : Nat) :
    silent Record285.machine (cost runs)
      (atLeftWord IncrementShift.returnState head (returnBits runs retained) right) =
      some (atLeftWord breakState (head-cost runs) retained (returnedRight runs right)) :=
  scan_return Record285.machine IncrementShift.returnState checkState breakState
    literal_rows runs head retained right

theorem cost_positive (runs : List Nat) : 0 < cost runs := by
  cases runs <;> simp [cost] <;> omega

theorem literal_return_physical (runs : List Nat) (head : Int) (retained right : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atLeftWord IncrementShift.returnState head (returnBits runs retained) right) physical) :
    Rel (atLeftWord breakState (head-cost runs) retained (returnedRight runs right))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (cost runs)) ∧
    ∀ t, t < cost runs →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_return runs head retained right)

/-- Complete selector, suffix shift, and return to break state when the shifted
left word has the specified return-scanner layout. This layout obligation is
explicit; it is not a source-level correctness theorem. -/
theorem selector_shift_return (selected suffix runs : List Nat) (last : Nat) (hbound : selected.length ≤ 16)
    (head : Int) (left retained farLeft : Nat)
    (hlayout : IncrementShift.shiftedLeft suffix (IncrementSelector.leftAfter selected left) =
      completeBits runs last farLeft) :
    silent Record285.machine
      (IncrementSelector.cost selected + IncrementShift.cost suffix + completeCost runs last)
      ⟨IncrementSelector.literalState selected.length,head,left,false,
        IncrementSelector.blocksBits selected (IncrementShift.suffixBits suffix retained)⟩ =
      some (atLeftWord breakState
        (head+IncrementSelector.cost selected+IncrementShift.cost suffix-2-completeCost runs last)
        farLeft (completeRight runs last (2*retained))) := by
  have hs := IncrementShift.selector_and_shift selected suffix hbound head left retained
  have hr := scan_complete Record285.machine IncrementShift.returnState checkState breakState
    literal_rows runs last (head+IncrementSelector.cost selected+IncrementShift.cost suffix-2)
    farLeft (2*retained)
  rw [silent_add, hs]
  simp only [Option.bind_some]
  simpa only [atLeftWord, ← hlayout] using hr

theorem selector_shift_return_physical (selected suffix runs : List Nat)
    (last : Nat) (hbound : selected.length ≤ 16) (head : Int) (left retained farLeft : Nat)
    (hlayout : IncrementShift.shiftedLeft suffix (IncrementSelector.leftAfter selected left) =
      completeBits runs last farLeft) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState selected.length,head,left,false,
      IncrementSelector.blocksBits selected (IncrementShift.suffixBits suffix retained)⟩ physical) :
    Rel (atLeftWord breakState
      (head+IncrementSelector.cost selected+IncrementShift.cost suffix-2-completeCost runs last)
      farLeft (completeRight runs last (2*retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run
        (IncrementSelector.cost selected + IncrementShift.cost suffix + completeCost runs last)) ∧
    ∀ t, t < IncrementSelector.cost selected + IncrementShift.cost suffix + completeCost runs last →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (selector_shift_return selected suffix runs last hbound head left retained farLeft hlayout)

/-- A unary push onto a zero-prefixed word, viewed from the new head. -/
theorem push_run (n x : Nat) :
    pushBit n true (2*x) = runPattern true n false x := by
  induction n with
  | zero => simp [pushBit,runPattern,bitVal]
  | succ n ih =>
    rw [pushBit,pushBit_affine,ih,runPattern]
    simp only [bitVal,if_true]
    omega

/-- A leading one extends the first run in a scanner layout. -/
theorem prepend_one_layout (runs : List Nat) (last farLeft : Nat) :
    ∃ runs' last', 1+2*completeBits runs last farLeft = completeBits runs' last' farLeft := by
  cases runs with
  | nil => exact ⟨[],last+1,by simp [completeBits,runPattern,bitVal]⟩
  | cons k ks => exact ⟨(k+1)::ks,last,by simp [completeBits,runPattern,bitVal]⟩

/-- Crossing a separator and pushing a nonempty unary run preserves the
leading-one scanner-layout invariant. -/
theorem push_field_layout (k : Nat) (runs : List Nat) (last farLeft : Nat) :
    pushBit (k+1) true (2*(1+2*completeBits runs last farLeft)) =
      1+2*completeBits (k::runs) last farLeft := by
  rw [push_run]
  simp only [runPattern,bitVal,if_true,completeBits]

theorem leftAfter_layout (blocks runs : List Nat) (last farLeft : Nat) :
    ∃ runs' last', IncrementSelector.leftAfter blocks (1+2*completeBits runs last farLeft) =
      1+2*completeBits runs' last' farLeft := by
  induction blocks generalizing runs last with
  | nil =>
    obtain ⟨runs',last',h⟩ := prepend_one_layout runs last farLeft
    exact ⟨runs',last',by simp only [IncrementSelector.leftAfter]; omega⟩
  | cons k ks ih =>
    simp only [IncrementSelector.leftAfter,push_field_layout]
    exact ih (k::runs) last

theorem shiftedLeft_layout (blocks runs : List Nat) (last farLeft : Nat) :
    ∃ runs' last', IncrementShift.shiftedLeft blocks (1+2*completeBits runs last farLeft) =
      1+2*completeBits runs' last' farLeft := by
  induction blocks generalizing runs last with
  | nil => exact ⟨runs,last,rfl⟩
  | cons k ks ih =>
    simp only [IncrementShift.shiftedLeft,push_field_layout]
    exact ih (k::runs) last

/-- Every nonempty selector list and every suffix have a valid complete
return layout when the starting cell and its left neighbor are zero. -/
theorem general_return_layout (gap : Nat) (selected suffix : List Nat) (farLeft : Nat) :
    ∃ runs last, IncrementShift.shiftedLeft suffix
      (IncrementSelector.leftAfter (gap::selected) (2*farLeft)) =
      completeBits runs last farLeft := by
  have hfirst : pushBit (gap+1) true (2*(2*farLeft)) =
      1+2*completeBits [] gap farLeft := by
    rw [push_run]
    simp only [runPattern,completeBits,bitVal,if_true]
  obtain ⟨runs,last,hleft⟩ := leftAfter_layout selected [] gap farLeft
  obtain ⟨runs',last',hshift⟩ := shiftedLeft_layout suffix runs last farLeft
  obtain ⟨runs'',last'',hfinish⟩ := prepend_one_layout runs' last' farLeft
  refine ⟨runs'',last'',?_⟩
  simp only [IncrementSelector.leftAfter,hfirst,hleft,hshift,hfinish]

/-- Full selector-to-break contract with the return layout derived from the
clean two-zero left boundary, for any nonempty selector and finite suffix. -/
theorem general_selector_shift_return_physical (gap : Nat) (selected suffix : List Nat)
    (hbound : (gap::selected).length ≤ 16) (head : Int) (retained farLeft : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState (gap::selected).length,head,2*farLeft,false,
      IncrementSelector.blocksBits (gap::selected) (IncrementShift.suffixBits suffix retained)⟩ physical) :
    ∃ runs last,
      Rel (atLeftWord breakState
        (head+IncrementSelector.cost (gap::selected)+IncrementShift.cost suffix-2-completeCost runs last)
        farLeft (completeRight runs last (2*retained)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run
          (IncrementSelector.cost (gap::selected) + IncrementShift.cost suffix + completeCost runs last)) ∧
      ∀ t, t < IncrementSelector.cost (gap::selected) + IncrementShift.cost suffix + completeCost runs last →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨runs,last,hlayout⟩ := general_return_layout gap selected suffix farLeft
  exact ⟨runs,last,selector_shift_return_physical (gap::selected) suffix runs last hbound head
    (2*farLeft) retained farLeft hlayout physical hrel⟩

/-- For the first field and no later fields, the clean left boundary supplies
the complete return layout for arbitrary run lengths and arbitrary far tape. -/
theorem first_field_layout (gap field farLeft : Nat) :
    IncrementShift.shiftedLeft []
      (IncrementSelector.leftAfter [gap,field] (2*farLeft)) =
      completeBits [field+2] gap farLeft := by
  simp only [IncrementShift.shiftedLeft,IncrementSelector.leftAfter,completeBits]
  rw [push_run, push_run]
  simp only [runPattern,bitVal,if_true]
  omega

/-- The first increment selector, with no remaining suffix fields, returns to
break state without a layout premise. Arbitrary tape beyond both boundary
zeros is preserved. -/
theorem first_field_return (gap field : Nat) (head : Int) (retained farLeft : Nat) :
    silent Record285.machine
      (IncrementSelector.cost [gap,field] + IncrementShift.cost [] + completeCost [field+2] gap)
      ⟨IncrementSelector.literalState 2,head,2*farLeft,false,
        IncrementSelector.blocksBits [gap,field] (IncrementShift.suffixBits [] retained)⟩ =
      some (atLeftWord breakState
        (head+IncrementSelector.cost [gap,field]+IncrementShift.cost []-2-completeCost [field+2] gap)
        farLeft (completeRight [field+2] gap (2*retained))) := by
  exact selector_shift_return [gap,field] [] [field+2] gap (by simp)
    head (2*farLeft) retained farLeft (first_field_layout gap field farLeft)

theorem first_field_return_physical (gap field : Nat) (head : Int) (retained farLeft : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementSelector.literalState 2,head,2*farLeft,false,
      IncrementSelector.blocksBits [gap,field] (IncrementShift.suffixBits [] retained)⟩ physical) :
    Rel (atLeftWord breakState
      (head+IncrementSelector.cost [gap,field]+IncrementShift.cost []-2-completeCost [field+2] gap)
      farLeft (completeRight [field+2] gap (2*retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run
        (IncrementSelector.cost [gap,field] + IncrementShift.cost [] + completeCost [field+2] gap)) ∧
    ∀ t, t < IncrementSelector.cost [gap,field] + IncrementShift.cost [] + completeCost [field+2] gap →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (first_field_return gap field head retained farLeft)

end Shared.PNP.Record285.IncrementReturn

import Shared.PNP.Record285.DecrementPreparation

/-! Full-tape decreasing selector for the literal ordinary decrement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementSelector
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (blocksBits cost odd_bit odd_tail)

/-- The selector writes the crossed zero; all unselected suffix bits remain. -/
def leftAfter : List Nat → Nat → Nat
  | [],left => 2*left
  | k::ks,left => leftAfter ks (pushBit (k+1) true (2*left))

structure Rows (M : Machine 285) (state : Nat → Fin 285) (limit : Nat) : Prop where
  crossing : ∀ d, d < limit → M.table.row (state (d+1)) false = ⟨false,.right,state d,false⟩
  scanning : ∀ d, d < limit → M.table.row (state (d+1)) true = ⟨true,.right,state (d+1),false⟩

/-- Traverse every preceding unary block and stop before the selected
field's first bit. Time, absolute head, and both complete half-tapes are exact. -/
theorem select (M : Machine 285) (state : Nat → Fin 285) (limit : Nat)
    (rows : Rows M state limit) (blocks : List Nat) (hbound : blocks.length+1 ≤ limit)
    (head : Int) (left tail : Nat) :
    silent M (cost blocks) ⟨state (blocks.length+1),head,left,false,blocksBits blocks tail⟩ =
      some ⟨state 0,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ := by
  induction blocks generalizing head left with
  | nil =>
    have hrow := rows.crossing 0 (by simp at hbound; omega)
    simp only [List.length_nil,Nat.zero_add,cost,blocksBits,leftAfter,silent,
      PhysicalNumeric.step,hrow,Bool.false_eq_true,if_false,bitVal,Nat.add_zero,Int.natCast_one]
  | cons k ks ih =>
    have hlen : ks.length+1 < limit := by simp only [List.length_cons] at hbound; omega
    have hnext : ks.length+1 ≤ limit := by omega
    have hrow := rows.crossing (ks.length+1) hlen
    have hscanrow := rows.scanning ks.length (by omega)
    have hfirst : silent M 1
        ⟨state ((ks.length+1)+1),head,left,false,blocksBits (k::ks) tail⟩ =
      some ⟨state (ks.length+1),head+1,2*left,true,runPattern true k false (blocksBits ks tail)⟩ := by
      simp only [blocksBits,silent,PhysicalNumeric.step,hrow,Bool.false_eq_true,if_false,
        odd_bit,odd_tail,bitVal,Nat.add_zero]
    have hscan := run_sweep_right M (state (ks.length+1)) true true hscanrow k false
      (blocksBits ks tail) (2*left) (head+1)
    have hrest := ih hnext ((head+1)+(k+1)) (pushBit (k+1) true (2*left))
    simp only [List.length_cons,cost,leftAfter]
    rw [show k+2+cost ks = 1+((k+1)+cost ks) by omega,silent_add,hfirst]
    simp only [Option.bind_some]
    rw [silent_add,hscan]
    simp only [Option.bind_some]
    have hhead : (head+1)+(k+1)+(cost ks:Int) = head+(1+((k+1)+cost ks):Nat) := by omega
    simpa only [Int.natCast_add,Int.natCast_one,hhead] using hrest

def state (d : Nat) : Fin 285 :=
  ⟨((IncrementSelector.literalState d).val-1) % 285,Nat.mod_lt _ (by decide)⟩

def rowCheck (d : Nat) : Bool :=
  decide (NumericTables.target.table.row (state (d+1)) false = ⟨false,.right,state d,false⟩) &&
  decide (NumericTables.target.table.row (state (d+1)) true = ⟨true,.right,state (d+1),false⟩)

theorem rows_checked : (List.range 16).all rowCheck = true := by decide

theorem literal_rows : Rows Record285.machine state 16 := by
  constructor <;> intro d hd
  · have h := List.all_eq_true.mp rows_checked d (List.mem_range.mpr hd)
    simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    simpa only [ArtifactEndpoint.literal_rows] using h.1
  · have h := List.all_eq_true.mp rows_checked d (List.mem_range.mpr hd)
    simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    simpa only [ArtifactEndpoint.literal_rows] using h.2

theorem literal_select (blocks : List Nat) (hbound : blocks.length+1 ≤ 16)
    (head : Int) (left tail : Nat) :
    silent Record285.machine (cost blocks)
      ⟨state (blocks.length+1),head,left,false,blocksBits blocks tail⟩ =
      some ⟨state 0,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ :=
  select Record285.machine state 16 literal_rows blocks hbound head left tail

theorem literal_select_physical (blocks : List Nat) (hbound : blocks.length+1 ≤ 16)
    (head : Int) (left tail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨state (blocks.length+1),head,left,false,blocksBits blocks tail⟩ physical) :
    Rel ⟨state 0,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (cost blocks)) ∧
    (∀ t, t < cost blocks → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < cost blocks := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (literal_select blocks hbound head left tail)
  refine ⟨hp.1,hp.2,?_⟩
  cases blocks <;> simp [cost] <;> omega

end Shared.PNP.Record285.DecrementSelector

import Shared.PNP.Record285.PhysicalSweeps
import Shared.PNP.Record285.ArtifactEndpoint

/-! Exact full-tape contracts for the ordinary increment selector. A run of
length `k+1` is represented by the natural parameter `k`; the unread suffix is
an arbitrary finite bit stream, including high bits beyond all selected fields.
The suffix-shift and lexical return stages are separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementSelector
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps

/-- Starting just right of a zero, encode nonempty unary runs and their zero
separators. `tail` contains every bit after the last separator. -/
def blocksBits : List Nat → Nat → Nat
  | [], tail => tail
  | k::ks, tail => 1+2*runPattern true k false (blocksBits ks tail)

/-- Exact number of transitions, including filling the selected zero. -/
def cost : List Nat → Nat
  | [] => 1
  | k::ks => k+2+cost ks

/-- The entire half-tape left of the head at the end of selection. -/
def leftAfter : List Nat → Nat → Nat
  | [], left => 2*left+1
  | k::ks, left => leftAfter ks (pushBit (k+1) true (2*left))

/-- Required rows for a decreasing selector chain, including flags. -/
structure Rows (M : Machine 285) (state : Nat → Fin 285) (limit : Nat) (next : Fin 285) : Prop where
  crossing : ∀ d, d < limit → M.table.row (state (d+1)) false = ⟨false,.right,state d,false⟩
  scanning : ∀ d, d ≤ limit → M.table.row (state d) true = ⟨true,.right,state d,false⟩
  final : M.table.row (state 0) false = ⟨true,.right,next,false⟩

@[simp] theorem odd_bit (n : Nat) : (1+2*n).testBit 0 = true := by
  simp [Nat.testBit_zero]

@[simp] theorem odd_tail (n : Nat) : (1+2*n)/2 = n := by omega

/-- Every admitted selector run terminates after `cost blocks` transitions,
including the increment's first write. The result gives the entire finite
half-tapes and absolute head position; no transition is marked. -/
theorem select (M : Machine 285) (state : Nat → Fin 285) (limit : Nat) (next : Fin 285)
    (rows : Rows M state limit next) (blocks : List Nat) (hbound : blocks.length ≤ limit)
    (head : Int) (left tail : Nat) :
    silent M (cost blocks) ⟨state blocks.length,head,left,false,blocksBits blocks tail⟩ =
      some ⟨next,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ := by
  induction blocks generalizing head left with
  | nil =>
    simp only [List.length_nil, cost, blocksBits, leftAfter]
    simp only [silent, PhysicalNumeric.step, rows.final, Bool.false_eq_true, if_false, bitVal,
      if_true, Int.natCast_one]
  | cons k ks ih =>
    have hlen : ks.length < limit := by simp only [List.length_cons] at hbound; omega
    have hnext : ks.length ≤ limit := by omega
    have hrow := rows.crossing ks.length hlen
    have hscanrow := rows.scanning ks.length hnext
    have hfirst : silent M 1
        ⟨state (ks.length+1),head,left,false,blocksBits (k::ks) tail⟩ =
      some ⟨state ks.length,head+1,2*left,true,runPattern true k false (blocksBits ks tail)⟩ := by
      simp only [blocksBits, silent, PhysicalNumeric.step, hrow, Bool.false_eq_true, if_false,
        odd_bit, odd_tail, bitVal, Nat.add_zero]
    have hscan := run_sweep_right M (state ks.length) true true hscanrow k false
      (blocksBits ks tail) (2*left) (head+1)
    have hrest := ih (by omega) ((head+1)+(k+1)) (pushBit (k+1) true (2*left))
    simp only [List.length_cons, cost, leftAfter]
    rw [show k+2+cost ks = 1+((k+1)+cost ks) by omega, silent_add, hfirst]
    simp only [Option.bind_some]
    rw [silent_add, hscan]
    simp only [Option.bind_some]
    have hhead : (head+1)+(k+1)+(cost ks:Int) = head+(1+((k+1)+cost ks):Nat) := by omega
    simpa only [Int.natCast_add, Int.natCast_one, hhead] using hrest

/-- The emitted selector controls in decreasing distance to the target.
Depth zero is the final `-2` state; depth `i+2` selects bank field `i`. -/
def literalState : Nat → Fin 285
  | 0 => ⟨14,by decide⟩
  | 1 => ⟨12,by decide⟩
  | 2 => ⟨16,by decide⟩
  | 3 => ⟨18,by decide⟩
  | 4 => ⟨30,by decide⟩
  | 5 => ⟨32,by decide⟩
  | 6 => ⟨34,by decide⟩
  | 7 => ⟨36,by decide⟩
  | 8 => ⟨38,by decide⟩
  | 9 => ⟨40,by decide⟩
  | 10 => ⟨42,by decide⟩
  | 11 => ⟨44,by decide⟩
  | 12 => ⟨20,by decide⟩
  | 13 => ⟨22,by decide⟩
  | 14 => ⟨24,by decide⟩
  | 15 => ⟨26,by decide⟩
  | 16 => ⟨28,by decide⟩
  | _ => ⟨14,by decide⟩

def shiftState : Fin 285 := ⟨50,by decide⟩

def rowCheck (d : Nat) : Bool :=
  decide (NumericTables.target.table.row (literalState d) true =
    ⟨true,.right,literalState d,false⟩) &&
  if d < 16 then decide (NumericTables.target.table.row (literalState (d+1)) false =
    ⟨false,.right,literalState d,false⟩) else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- Each state and both relevant rows are checked against the literal table's
previously proved numeric copy. -/
theorem rowCheck_all : (List.range 17).all rowCheck = true := by decide

theorem checked_row (d : Nat) (hd : d < 17) : rowCheck d = true :=
  List.all_eq_true.mp rowCheck_all d (List.mem_range.mpr hd)

/-- Literal selector rows, with the full finite range of physical indices. -/
theorem literal_rows : Rows Record285.machine literalState 16 shiftState := by
  constructor
  · intro d hd
    have h := checked_row d (by omega)
    simp only [rowCheck, Bool.and_eq_true] at h
    have hx := h.2
    simp only [if_pos hd, decide_eq_true_eq] at hx
    rw [ArtifactEndpoint.literal_rows]
    exact hx
  · intro d hd
    have h := checked_row d (by omega)
    simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ArtifactEndpoint.literal_rows]
    exact h.1
  · rw [ArtifactEndpoint.literal_rows]
    decide

/-- Unconditional numeric execution for each of the 15 emitted increment
selectors, with arbitrary unary block lengths and arbitrary retained suffix. -/
theorem literal_select (blocks : List Nat) (hbound : blocks.length ≤ 16)
    (head : Int) (left tail : Nat) :
    silent Record285.machine (cost blocks)
      ⟨literalState blocks.length,head,left,false,blocksBits blocks tail⟩ =
      some ⟨shiftState,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ :=
  select Record285.machine literalState 16 shiftState literal_rows blocks hbound head left tail

theorem cost_positive (blocks : List Nat) : 0 < cost blocks := by
  cases blocks <;> simp [cost] <;> omega

/-- Literal execution on the ordinary integer-indexed physical tape. The
relation accounts for every cell and every retained high suffix. -/
theorem literal_select_physical (blocks : List Nat) (hbound : blocks.length ≤ 16)
    (head : Int) (left tail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨literalState blocks.length,head,left,false,blocksBits blocks tail⟩ physical) :
    Rel ⟨shiftState,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (cost blocks)) ∧
    ∀ t, t < cost blocks →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_select blocks hbound head left tail)

/-- Physical field indices zero through fourteen correspond to selector depths
`i+2`. The preceding blocks include the prepared gap and anchor. -/
theorem literal_select_field (i : Nat) (hi : i < 15) (blocks : List Nat)
    (hlen : blocks.length = i+2) (head : Int) (left tail : Nat) :
    silent Record285.machine (cost blocks)
      ⟨literalState (i+2),head,left,false,blocksBits blocks tail⟩ =
      some ⟨shiftState,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ := by
  have h := literal_select blocks (by omega) head left tail
  simpa only [hlen] using h

end Shared.PNP.Record285.IncrementSelector

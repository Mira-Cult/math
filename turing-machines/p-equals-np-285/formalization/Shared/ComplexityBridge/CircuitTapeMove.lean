import Shared.ComplexityBridge.CircuitRelocate
import Shared.Codes.FinitePrograms

/-! Explicit bounded tape-movement circuits. Input contains the write bit,
direction, and a bounded window of the shared finite-program tape. The
construction uses blank `false` outside the window. -/
namespace Shared.ComplexityBridge.CircuitTapeMove
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CircuitRelocate
open Shared.Codes.FinitePrograms

/-- The first two wires are write and leftward; then n left cells, the current
cell and n right cells. -/
def width (n : Nat) : Nat := 3+2*n

def inputBit (n : Nat) (written leftward : Bool) (tape : Tape) (i : Nat) : Bool :=
  if i = 0 then written else if i = 1 then leftward else
  if i < 2+n then (tape.1[i-2]?).getD false else
  if i = 2+n then tape.2.1 else (tape.2.2[i-(3+n)]?).getD false

def inputWires (n : Nat) (written leftward : Bool) (tape : Tape) : List Bool :=
  seed (width n) (inputBit n written leftward tape)

theorem inputWires_length (n : Nat) (written leftward : Bool) (tape : Tape) :
    (inputWires n written leftward tape).length = width n := seed_length _ _

theorem inputWires_bit (n : Nat) (written leftward : Bool) (tape : Tape) (i : Nat)
    (hi : i < width n) : wire (inputWires n written leftward tape) i = inputBit n written leftward tape i :=
  seed_wire _ _ _ hi

/-- The first component is used for a leftward move, the second for rightward. -/
def pairAt (n i : Nat) : Nat × Nat :=
  if i < n then
    (if i+1 < n then 2+i+1 else width n,
     if i = 0 then 0 else 2+(i-1))
  else if i = n then
    (if n = 0 then width n else 2, if n = 0 then width n else 3+n)
  else
    let j := i-n-1
    (if j = 0 then 0 else 3+n+(j-1),
     if j+1 < n then 3+n+j+1 else width n)

def pairs (n : Nat) : List (Nat × Nat) := (List.range (2*n+1)).map (pairAt n)

theorem pairs_length (n : Nat) : (pairs n).length = 2*n+1 := by simp [pairs]

theorem pairAt_bound (n i : Nat) (hi : i < 2*n+1) :
    (pairAt n i).1 < width n+1 ∧ (pairAt n i).2 < width n+1 := by
  unfold pairAt width
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> (try split_ifs) <;> omega

theorem pairs_bound (n : Nat) : ∀ p ∈ pairs n, p.1 < width n+1 ∧ p.2 < width n+1 := by
  intro p hp
  simp only [pairs,List.mem_map,List.mem_range] at hp
  obtain ⟨i,hi,rfl⟩ := hp
  exact pairAt_bound n i hi

/-- One explicit blank gate followed by four selector gates for each output. -/
def moveGates (n : Nat) : List Gate :=
  [.constant false] ++ muxes (width n+1) 1 (pairs n)

def outputIndex (n i : Nat) : Nat := width n+1+4*i+3

theorem moveGates_length (n : Nat) : (moveGates n).length = 1+4*(2*n+1) := by
  simp [moveGates,muxes_length,pairs_length,Nat.add_comm]

theorem moveGates_valid (n : Nat) : validGates (width n) (moveGates n) := by
  simp only [moveGates,validGates_append,List.length_cons,List.length_nil]
  constructor
  · simp [validGates,validGate]
  · apply muxes_valid
    · simp [width]
    · simpa using pairs_bound n

theorem pairs_get (n i : Nat) (hi : i < 2*n+1) : (pairs n)[i]? = some (pairAt n i) := by
  simp [pairs,hi]

/-- The constructed gate list selects the indicated source wire for every
output of the bounded tape window. -/
theorem moveGates_simulate (n : Nat) (written leftward : Bool) (tape : Tape)
    (i : Nat) (hi : i < 2*n+1) :
    wire (simulate (inputWires n written leftward tape) (moveGates n)) (outputIndex n i) =
      if leftward then wire (inputWires n written leftward tape ++ [false]) (pairAt n i).1
      else wire (inputWires n written leftward tape ++ [false]) (pairAt n i).2 := by
  let wires := inputWires n written leftward tape
  let mid := wires ++ [false]
  have hw : wires.length = width n := inputWires_length n written leftward tape
  have hm : mid.length = width n+1 := by simp [mid,hw]
  have hs : 1 < mid.length := by rw [hm]; simp [width]
  have hp : ∀ p ∈ pairs n, p.1 < mid.length ∧ p.2 < mid.length := by rw [hm]; exact pairs_bound n
  have h := muxes_simulate mid 1 (pairs n) hs hp i (pairAt n i).1 (pairAt n i).2
    (by simpa using pairs_get n i hi)
  have hd : wire mid 1 = leftward := by
    rw [wire_append wires [false] 1 (by rw [hw]; simp [width]; omega)]
    rw [inputWires_bit n written leftward tape 1 (by simp [width]; omega)]
    simp [inputBit]
  rw [hm,hd] at h
  simpa [moveGates,simulate,evalGate,outputIndex,mid,wires,hw] using h

/-- The output representation contains n cells on each side and the head. -/
def tapeView (n : Nat) (tape : Tape) (i : Nat) : Bool :=
  if i < n then (tape.1[i]?).getD false else
  if i = n then tape.2.1 else (tape.2.2[i-n-1]?).getD false

theorem mid_blank (n : Nat) (w d : Bool) (t : Tape) :
    wire (inputWires n w d t ++ [false]) (width n) = false := by
  have h := wire_last (inputWires n w d t) false
  simpa [inputWires_length] using h

theorem mid_write (n : Nat) (w d : Bool) (t : Tape) :
    wire (inputWires n w d t ++ [false]) 0 = w := by
  rw [wire_append _ _ 0 (by simp [inputWires_length,width])]
  rw [inputWires_bit n w d t 0 (by simp [width])]
  simp [inputBit]

theorem mid_left (n : Nat) (w d : Bool) (t : Tape) (i : Nat) (hi : i < n) :
    wire (inputWires n w d t ++ [false]) (2+i) = (t.1[i]?).getD false := by
  have hx : 2+i < width n := by simp [width]; omega
  rw [wire_append _ _ (2+i) (by simpa [inputWires_length] using hx),inputWires_bit n w d t (2+i) hx]
  have h0 : 2+i ≠ 0 := by omega
  have h1 : 2+i ≠ 1 := by omega
  have h2 : 2+i < 2+n := by omega
  simp [inputBit,h0,h1,h2]

theorem mid_right (n : Nat) (w d : Bool) (t : Tape) (i : Nat) (hi : i < n) :
    wire (inputWires n w d t ++ [false]) (3+n+i) = (t.2.2[i]?).getD false := by
  have hx : 3+n+i < width n := by simp [width]; omega
  rw [wire_append _ _ (3+n+i) (by simpa [inputWires_length] using hx),inputWires_bit n w d t (3+n+i) hx]
  have h0 : 3+n+i ≠ 0 := by omega
  have h1 : 3+n+i ≠ 1 := by omega
  have h2 : ¬ 3+n+i < 2+n := by omega
  have h3 : 3+n+i ≠ 2+n := by omega
  simp only [inputBit,if_neg h0,if_neg h1,if_neg h2,if_neg h3]
  have he : 3+n+i-(3+n) = i := by omega
  rw [he]

theorem tail_getD (xs : List Bool) (i : Nat) :
    (xs.tail[i]?).getD false = (xs[i+1]?).getD false := by
  cases xs <;> simp

theorem getD_outside (xs : List Bool) (n i : Nat) (hlen : xs.length ≤ n) (hi : n ≤ i) :
    (xs[i]?).getD false = false := by
  have h : xs[i]? = none := List.getElem?_eq_none (by omega)
  simp [h]

/-- The left portion of the output window agrees with the shared tape move. -/
theorem move_left_correct (n : Nat) (w d : Bool) (t : Tape) (i : Nat)
    (hi : i < n) (hl : t.1.length ≤ n) :
    wire (simulate (inputWires n w d t) (moveGates n)) (outputIndex n i) =
      tapeView n (moveTape d w t) i := by
  rw [moveGates_simulate n w d t i (by omega)]
  cases d with
  | false =>
    cases i with
    | zero =>
      simp [pairAt,hi,tapeView,moveTape,mid_write]
    | succ i =>
      have his : i < n := by omega
      have he : 2+(i+1-1) = 2+i := by omega
      simp only [Bool.false_eq_true,if_false,pairAt,if_pos hi,Prod.snd,
        Nat.succ_ne_zero,if_neg,he,tapeView,moveTape]
      rw [mid_left n w false t i his]
      simp [hi]
  | true =>
    by_cases hs : i+1 < n
    · have he : 2+i+1 = 2+(i+1) := by omega
      simp only [if_true,pairAt,if_pos hi,Prod.fst,if_pos hs,he]
      rw [mid_left n w true t (i+1) hs]
      simp [tapeView,moveTape,hi,tail_getD]
    · simp only [if_true,pairAt,if_pos hi,Prod.fst,if_neg hs]
      rw [mid_blank]
      simp only [tapeView,if_pos hi,moveTape,if_true,Prod.fst,tail_getD]
      symm
      exact getD_outside t.1 n (i+1) hl (by omega)

theorem head_get (xs : List Bool) : xs[0]? = xs.head? := by cases xs <;> rfl

/-- The new head is selected from the left or right neighbor; an empty
window is sound only when both represented stacks are empty. -/
theorem move_head_correct (n : Nat) (w d : Bool) (t : Tape)
    (hl : t.1.length ≤ n) (hr : t.2.2.length ≤ n) :
    wire (simulate (inputWires n w d t) (moveGates n)) (outputIndex n n) =
      tapeView n (moveTape d w t) n := by
  rw [moveGates_simulate n w d t n (by omega)]
  cases n with
  | zero =>
    have hleft : t.1 = [] := List.length_eq_zero_iff.mp (by omega)
    have hright : t.2.2 = [] := List.length_eq_zero_iff.mp (by omega)
    cases d <;> simp [pairAt,mid_blank,tapeView,moveTape,hleft,hright]
  | succ n =>
    have hn : 0 < n+1 := by omega
    have hlbit : wire (inputWires (n+1) w d t ++ [false]) 2 = t.1.head?.getD false := by
      simpa [head_get] using mid_left (n+1) w d t 0 hn
    have hrbit : wire (inputWires (n+1) w d t ++ [false]) (3+(n+1)) = t.2.2.head?.getD false := by
      simpa [head_get] using mid_right (n+1) w d t 0 hn
    cases d <;> simp [pairAt,hlbit,hrbit,tapeView,moveTape]

/-- The right portion of the window agrees with the shared tape move. -/
theorem move_right_correct (n : Nat) (w d : Bool) (t : Tape) (j : Nat)
    (hj : j < n) (hr : t.2.2.length ≤ n) :
    wire (simulate (inputWires n w d t) (moveGates n)) (outputIndex n (n+1+j)) =
      tapeView n (moveTape d w t) (n+1+j) := by
  rw [moveGates_simulate n w d t (n+1+j) (by omega)]
  have hnot : ¬ n+1+j < n := by omega
  have hne : n+1+j ≠ n := by omega
  have hidx : n+1+j-n-1 = j := by omega
  cases d with
  | false =>
    by_cases hs : j+1 < n
    · have he : 3+n+j+1 = 3+n+(j+1) := by omega
      simp only [Bool.false_eq_true,if_false,pairAt,if_neg hnot,if_neg hne,hidx,Prod.snd,if_pos hs,he]
      rw [mid_right n w false t (j+1) hs]
      simp [tapeView,moveTape,hnot,hne,hidx,tail_getD]
    · simp only [Bool.false_eq_true,if_false,pairAt,if_neg hnot,if_neg hne,hidx,Prod.snd,if_neg hs]
      rw [mid_blank]
      have hz := getD_outside t.2.2 n (j+1) hr (by omega)
      simp [tapeView,moveTape,hnot,hne,hidx,tail_getD,hz]
  | true =>
    cases j with
    | zero =>
      simp [pairAt,hnot,hne,hidx,tapeView,moveTape,mid_write]
    | succ j =>
      have hjs : j < n := by omega
      have he : 3+n+(j+1-1) = 3+n+j := by omega
      simp only [if_true,pairAt,if_neg hnot,if_neg hne,hidx,Prod.fst,
        Nat.succ_ne_zero,if_neg,he,tapeView,moveTape]
      simp only [if_false]
      rw [mid_right n w true t j hjs]
      simp [hnot,hne,hidx]

/-- Every output bit agrees with the actual bounded tape transition. -/
theorem move_correct (n : Nat) (w d : Bool) (t : Tape) (i : Nat)
    (hi : i < 2*n+1) (hl : t.1.length ≤ n) (hr : t.2.2.length ≤ n) :
    wire (simulate (inputWires n w d t) (moveGates n)) (outputIndex n i) =
      tapeView n (moveTape d w t) i := by
  by_cases hleft : i < n
  · exact move_left_correct n w d t i hleft hl
  · by_cases heq : i = n
    · subst i; exact move_head_correct n w d t hl hr
    · have hn : n+1 ≤ i := by omega
      let j := i-(n+1)
      have hj : j < n := by dsimp [j]; omega
      have hidx : n+1+j = i := by dsimp [j]; omega
      simpa [hidx] using move_right_correct n w d t j hj hr

/-- Keep write and direction wires and expose all updated tape-window bits. -/
def outputs (n : Nat) : List Nat :=
  0 :: 1 :: (List.range (2*n+1)).map (outputIndex n)

theorem outputs_length (n : Nat) : (outputs n).length = width n := by
  simp [outputs,width]; omega

theorem outputs_bound (n : Nat) : ∀ o ∈ outputs n, o < width n+(moveGates n).length := by
  intro o ho
  simp only [outputs,List.mem_cons,List.mem_map,List.mem_range] at ho
  rcases ho with rfl | rfl | ⟨i,hi,rfl⟩
  · simp [width,moveGates_length] <;> omega
  · simp [width,moveGates_length] <;> omega
  · simp only [outputIndex,moveGates_length]
    omega

/-- The entire state-update vector represents the shared machine tape move. -/
theorem move_stepState (n : Nat) (w d : Bool) (t : Tape)
    (hl : t.1.length ≤ n) (hr : t.2.2.length ≤ n) :
    stepState (moveGates n) (outputs n) (inputWires n w d t) =
      w :: d :: (List.range (2*n+1)).map (tapeView n (moveTape d w t)) := by
  have h0 : wire (simulate (inputWires n w d t) (moveGates n)) 0 = w := by
    rw [wire_simulate _ _ 0 (by simp [inputWires_length,width])]
    rw [inputWires_bit n w d t 0 (by simp [width])]
    simp [inputBit]
  have h1 : wire (simulate (inputWires n w d t) (moveGates n)) 1 = d := by
    rw [wire_simulate _ _ 1 (by simp [inputWires_length,width] <;> omega)]
    rw [inputWires_bit n w d t 1 (by simp [width] <;> omega)]
    simp [inputBit]
  simp only [stepState,outputs,List.map_cons,List.map_map,h0,h1]
  congr 2
  apply List.map_congr_left
  intro i hi
  exact move_correct n w d t i (List.mem_range.mp hi) hl hr

theorem inputBit_view (n : Nat) (w d : Bool) (t : Tape) (j : Nat) :
    inputBit n w d t (2+j) = tapeView n t j := by
  have h0 : 2+j ≠ 0 := by omega
  have h1 : 2+j ≠ 1 := by omega
  have hlt : (2+j < 2+n) ↔ j < n := by omega
  have heq : (2+j = 2+n) ↔ j = n := by omega
  have hl : 2+j-2 = j := by omega
  have hr : 2+j-(3+n) = j-n-1 := by omega
  simp only [inputBit,if_neg h0,if_neg h1,hlt,heq,hl,hr,tapeView]

/-- The circuit's output layout is the same input layout used for the next
copy, retaining the selected write and direction bits. -/
theorem inputWires_view (n : Nat) (w d : Bool) (t : Tape) :
    inputWires n w d t = w :: d :: (List.range (2*n+1)).map (tapeView n t) := by
  apply List.ext_getElem
  · simp [inputWires_length,width]; omega
  · intro i hi₁ hi₂
    rw [← wire_get _ i hi₁, inputWires_bit n w d t i (by simpa [inputWires_length] using hi₁)]
    cases i with
    | zero => simp [inputBit]
    | succ i =>
      cases i with
      | zero => simp [inputBit]
      | succ j =>
        have hj : j < 2*n+1 := by simp [inputWires_length,width] at hi₁; omega
        simp only [List.getElem_cons_succ,List.getElem_map,List.getElem_range]
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using inputBit_view n w d t j

/-- The movement circuit gives the same encoded output as one tape move.
To iterate faithfully, each subsequent input tape must also fit the window. -/
theorem move_stepState_inputWires (n : Nat) (w d : Bool) (t : Tape)
    (hl : t.1.length ≤ n) (hr : t.2.2.length ≤ n) :
    stepState (moveGates n) (outputs n) (inputWires n w d t) =
      inputWires n w d (moveTape d w t) := by
  rw [inputWires_view n w d (moveTape d w t)]
  exact move_stepState n w d t hl hr

/-- Repeat the same movement command; this is not a whole-program execution. -/
def runTape (w d : Bool) : Nat → Tape → Tape
  | 0, t => t
  | k+1, t => runTape w d k (moveTape d w t)

/-- Every tape inspected by the next k moves fits the represented window. -/
def FitsFor (n : Nat) (w d : Bool) : Nat → Tape → Prop
  | 0, _ => True
  | k+1, t => t.1.length ≤ n ∧ t.2.2.length ≤ n ∧ FitsFor n w d k (moveTape d w t)

/-- A single movement grows either side by at most one cell. -/
theorem moveTape_lengths (w d : Bool) (t : Tape) :
    (moveTape d w t).1.length ≤ t.1.length+1 ∧
      (moveTape d w t).2.2.length ≤ t.2.2.length+1 := by
  cases d <;> simp [moveTape,List.length_tail] <;> omega

/-- A window containing the original tape plus one cell per remaining step
satisfies the finite-window invariant for every step. -/
theorem fitsFor_of_slack (n : Nat) (w d : Bool) (k : Nat) (t : Tape)
    (hl : t.1.length+k ≤ n) (hr : t.2.2.length+k ≤ n) : FitsFor n w d k t := by
  induction k generalizing t with
  | zero => trivial
  | succ k ih =>
    simp only [FitsFor]
    have hm := moveTape_lengths w d t
    refine ⟨by omega, by omega, ?_⟩
    apply ih (moveTape d w t) <;> omega

theorem runState_move (n : Nat) (w d : Bool) (k : Nat) (t : Tape)
    (hf : FitsFor n w d k t) :
    runState (moveGates n) (outputs n) k (inputWires n w d t) =
      inputWires n w d (runTape w d k t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [FitsFor] at hf
    simp only [runState,runTape]
    rw [move_stepState_inputWires n w d t hf.1 hf.2.1]
    exact ih (moveTape d w t) hf.2.2

theorem readState_identity (wires : List Bool) (n : Nat) (hw : wires.length = n) :
    readState wires n (List.range n) = wires := by
  apply List.ext_getElem
  · simp [readState_length,hw]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [readState_length] using hi₁
    rw [← wire_get _ i hi₁,readState_wire _ _ _ i hi]
    simp only [List.getElem?_range,hi,if_true,Option.getD_some]
    exact wire_get wires i hi₂

/-- Unrolling the actual movement circuit simulates repeated moves while the
stated finite-window invariant holds. -/
theorem unroll_move (n : Nat) (w d : Bool) (k : Nat) (t : Tape)
    (hf : FitsFor n w d k t) :
    readState
      (simulate (inputWires n w d t)
        (unroll (width n) (moveGates n) (outputs n) (width n) (List.range (width n)) k))
      (width n) (finalRefs (width n) (moveGates n) (outputs n) (width n) (List.range (width n)) k) =
    inputWires n w d (runTape w d k t) := by
  have hw := inputWires_length n w d t
  have hin : ∀ i < width n, ((List.range (width n))[i]?).getD 0 < (inputWires n w d t).length := by
    intro i hi
    simp [hi,hw]
  have h := unroll_readState (inputWires n w d t) (width n) (List.range (width n))
    (outputs n) (moveGates n) hin (moveGates_valid n) (outputs_length n) (outputs_bound n) k
  rw [hw,readState_identity _ _ hw,runState_move n w d k t hf] at h
  exact h

/-- The repeated-movement theorem with a concrete, sufficient window bound. -/
theorem unroll_move_with_slack (n : Nat) (w d : Bool) (k : Nat) (t : Tape)
    (hl : t.1.length+k ≤ n) (hr : t.2.2.length+k ≤ n) :
    readState
      (simulate (inputWires n w d t)
        (unroll (width n) (moveGates n) (outputs n) (width n) (List.range (width n)) k))
      (width n) (finalRefs (width n) (moveGates n) (outputs n) (width n) (List.range (width n)) k) =
    inputWires n w d (runTape w d k t) :=
  unroll_move n w d k t (fitsFor_of_slack n w d k t hl hr)

theorem unroll_move_length (n k : Nat) :
    (unroll (width n) (moveGates n) (outputs n) (width n) (List.range (width n)) k).length =
      k*(1+4*(2*n+1)) := by
  rw [unroll_length,moveGates_length]

namespace Fixtures
example : tapeView 0 (moveTape true true ([],false,[])) 0 = false := by decide
example : wire (simulate (inputWires 0 true true ([],false,[])) (moveGates 0)) (outputIndex 0 0) = false := by decide
example : stepState (moveGates 1) (outputs 1) (inputWires 1 true true ([true],false,[false])) =
    [true,true,false,true,true] := by decide
example : stepState (moveGates 1) (outputs 1) (inputWires 1 true false ([false],true,[true])) =
    [true,false,true,true,false] := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitTapeMove

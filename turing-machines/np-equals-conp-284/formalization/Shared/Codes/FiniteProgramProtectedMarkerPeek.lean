import Shared.Codes.FiniteProgramProtectedScan
import Shared.Codes.FiniteProgramTaggedLoop

/-! Read a protected block's marker and return to its data bit without
altering either the block or the buffer on its right. The payload width is
compiled into finite control. This pass does not check the occupancy flag. -/
namespace Shared.Codes.FiniteProgramProtectedMarkerPeek
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def flag (b : Bool) : Fin 2 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
def state (i : Nat) (m : Fin 2) : Nat := 2*i+m.val

def row (width i : Nat) (m : Fin 2) (read : Bool) : Row :=
  if i < width+1 then (read,false,state (i+1) m,0)
  else if i = width+1 then (read,true,state (i+1) (flag read),0)
  else if i < 2*width+2 then (read,true,state (i+1) m,0)
  else (read,true,0,1)

def rowPair (width : Nat) (q : Fin (2*(2*width+3))) : Row × Row :=
  let i := q.val / 2
  let m : Fin 2 := ⟨q.val % 2,by omega⟩
  (row width i m false,row width i m true)

def program (width : Nat) : Program := List.ofFn (rowPair width)

@[simp] theorem program_length (width : Nat) : (program width).length = 4*width+6 := by
  simp [program]
  omega

theorem state_bound (width i : Nat) (m : Fin 2) (hi : i ≤ 2*width+2) :
    state i m < (program width).length := by
  have hm := m.isLt
  simp only [program_length,state]
  omega

/-- The two terminal states carry different marker values. -/
theorem marker_states_distinct (width : Nat) :
    state (2*width+2) (flag false) ≠ state (2*width+2) (flag true) := by
  simp [state,flag]

theorem row_at (width i : Nat) (m : Fin 2) (hi : i ≤ 2*width+2) :
    (program width)[state i m]? = some (row width i m false,row width i m true) := by
  have hb := state_bound width i m hi
  rw [List.getElem?_eq_getElem hb]
  simp only [program,List.getElem_ofFn,rowPair]
  have hd : (2*i+m.val)/2 = i := by have hm := m.isLt; omega
  have hr : (2*i+m.val)%2 = m.val := by have hm := m.isLt; omega
  simp [state,hd,hr]

/-- Every generated destination is within the finite table. -/
theorem program_valid (width : Nat) : valid (program width) = true := by
  have hn : (program width).isEmpty = false := by
    cases h : program width with
    | nil => have hl := program_length width; rw [h] at hl; simp at hl
    | cons r rs => rfl
  have hall : (program width).all
      (fun r => validRow (program width).length r.1 && validRow (program width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    change r ∈ List.ofFn (rowPair width) at hr
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    have hbound : ∀ i : Nat, i < 2*width+2 → ∀ m : Fin 2,
        state (i+1) m < 4*width+6 := by
      intro i hi m
      have hm := m.isLt
      simp only [state]
      omega
    simp only [program_length,rowPair]
    have hflag : ∀ b, (flag b).val < 2 := fun b => (flag b).isLt
    simp only [row]
    split
    · rename_i hleft
      have hi : q.val/2 < 2*width+2 := by omega
      simp [validRow,hbound _ hi]
    · rename_i hleft
      split
      · rename_i hmark
        have hi : q.val/2 < 2*width+2 := by omega
        simp [validRow,hbound _ hi]
      · split
        · rename_i hright
          simp [validRow,hbound _ hright]
        · simp [validRow]
  change (!(program width).isEmpty && (program width).all
    (fun r => validRow (program width).length r.1 && validRow (program width).length r.2)) = true
  rw [hn,hall]
  rfl

theorem step_left (width i : Nat) (m : Fin 2) (bit : Bool)
    (hi : i < width+1) (L R : List Bool) :
    step (program width) (state i m,tapeLeft (bit::L) R) =
      some (.inr (state (i+1) m,tapeLeft L (bit::R))) := by
  have hr := row_at width i m (by omega)
  cases bit <;> simp [step,hr,row,hi,tapeLeft,moveTape]

theorem step_marker (width : Nat) (m : Fin 2) (bit : Bool) (L R : List Bool) :
    step (program width) (state (width+1) m,tapeAt L (bit::R)) =
      some (.inr (state (width+2) (flag bit),tapeAt (bit::L) R)) := by
  have hr := row_at width (width+1) m (by omega)
  cases bit <;> simp [step,hr,row,tapeAt,moveTape]

theorem step_right (width i : Nat) (m : Fin 2) (bit : Bool)
    (hlo : width+2 ≤ i) (hi : i < 2*width+2) (L R : List Bool) :
    step (program width) (state i m,tapeAt L (bit::R)) =
      some (.inr (state (i+1) m,tapeAt (bit::L) R)) := by
  have hr := row_at width i m (by omega)
  have hl : ¬ i < width+1 := by omega
  have hm : i ≠ width+1 := by omega
  cases bit <;> simp [step,hr,row,hl,hm,hi,tapeAt,moveTape]

theorem terminal_placeholder (width : Nat) (b : Bool) (t : Tape) :
    step (program width) (state (2*width+2) (flag b),t) = some (.inl false) := by
  have hr := row_at width (2*width+2) (flag b) (by omega)
  have ha : ¬ 2*width+2 < width+1 := by omega
  have hb : 2*width+2 ≠ width+1 := by omega
  simp only [row,if_neg ha,if_neg hb,lt_self_iff_false,if_false] at hr
  cases h : t.2.1 <;> simp [step,hr,h]

theorem left_pass (width i : Nat) (m : Fin 2) (xs L R : List Bool)
    (hi : i+xs.length ≤ width+1) :
    run (program width) (state i m,tapeLeft (xs++L) R) xs.length =
      some (.inr (state (i+xs.length) m,tapeLeft L (xs.reverse++R))) := by
  induction xs generalizing i R with
  | nil => simp
  | cons b xs ih =>
    have hstep := step_left width i m b (by simp only [List.length_cons] at hi; omega) (xs++L) R
    have hrun : run (program width) (state i m,tapeLeft ((b::xs)++L) R) 1 =
        some (.inr (state (i+1) m,tapeLeft (xs++L) (b::R))) := by
      simpa [run,advance] using hstep
    have ht := ih (i+1) (b::R) (by simp only [List.length_cons] at hi; omega)
    rw [show (b::xs).length = 1+xs.length by simp [Nat.add_comm],run_continue _ _ _ 1 _ hrun]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem right_pass (width i : Nat) (m : Fin 2) (xs L R : List Bool)
    (hlo : width+2 ≤ i) (hi : i+xs.length ≤ 2*width+2) :
    run (program width) (state i m,tapeAt L (xs++R)) xs.length =
      some (.inr (state (i+xs.length) m,tapeAt (xs.reverse++L) R)) := by
  induction xs generalizing i L with
  | nil => simp
  | cons b xs ih =>
    have hstep := step_right width i m b hlo (by simp only [List.length_cons] at hi; omega) L (xs++R)
    have hrun : run (program width) (state i m,tapeAt L ((b::xs)++R)) 1 =
        some (.inr (state (i+1) m,tapeAt (b::L) (xs++R))) := by
      simpa [run,advance] using hstep
    have ht := ih (i+1) (b::L) (by omega) (by simp only [List.length_cons] at hi; omega)
    rw [show (b::xs).length = 1+xs.length by simp [Nat.add_comm],run_continue _ _ _ 1 _ hrun]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

/-- Read the marker at a fixed offset and return to the original data cell.
Both the data and the entire tape are unchanged; only the terminal state
depends on the marker. The caller supplies the protected layout and checks
its occupancy separately. -/
theorem peek (width : Nat) (data marked : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) :
    run (program width) (0,tapeLeft (data::(payload ++ marked::L)) R) (2*width+2) =
      some (.inr (state (2*width+2) (flag marked),
        tapeLeft (data::(payload ++ marked::L)) R)) := by
  let xs := data::payload
  have hl := left_pass width 0 (flag false) xs (marked::L) R (by simp [xs,hlen])
  have hl' : run (program width) (0,tapeLeft (data::(payload ++ marked::L)) R) (width+1) =
      some (.inr (state (width+1) (flag false),tapeAt L (marked::(payload.reverse ++ data::R)))) := by
    simpa [xs,hlen,state,flag,tapeLeft,tapeAt,List.reverse_cons,List.append_assoc] using hl
  have hm := step_marker width (flag false) marked L (payload.reverse ++ data::R)
  have hm' : run (program width)
      (state (width+1) (flag false),tapeAt L (marked::(payload.reverse ++ data::R))) 1 =
      some (.inr (state (width+2) (flag marked),tapeAt (marked::L) (payload.reverse ++ data::R))) := by
    simpa [run,advance] using hm
  have hr := right_pass width (width+2) (flag marked) payload.reverse (marked::L) (data::R)
    (by omega) (by simp [hlen]; omega)
  rw [show 2*width+2 = (width+1)+(1+width) by omega,
    run_continue _ _ _ _ _ hl',run_continue _ _ _ 1 _ hm']
  simpa [hlen,state,tapeLeft,tapeAt,List.reverse_reverse,List.append_assoc,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

/-- Specialization to a data cell whose left side contains the protected
payload, marker, and occupied bit, and whose right side is a tagged buffer.
The occupied bit is preserved but is not inspected by this pass. -/
theorem peek_protected (width : Nat) (data marked : Bool) (payload L xs : List Bool)
    (hlen : payload.length = width) :
    run (program width)
        (Shared.Codes.FiniteProgramTaggedLoop.canonical (payload ++ marked::true::L) data xs)
        (2*width+2) =
      some (.inr (state (2*width+2) (flag marked),
        (Shared.Codes.FiniteProgramTaggedLoop.canonical (payload ++ marked::true::L) data xs).2)) := by
  have h := peek width data marked payload (true::L)
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false]) hlen
  simpa [Shared.Codes.FiniteProgramTaggedLoop.canonical,tapeLeft,tapeAt,List.append_assoc] using h

/-- The same finite pass works on any representation of the same infinite
tape, including tapes with additional blank padding. -/
theorem peek_related (width : Nat) (data marked : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) (t : Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t
      (tapeLeft (data::(payload ++ marked::L)) R)) :
    ∃ u, run (program width) (0,t) (2*width+2) =
        some (.inr (state (2*width+2) (flag marked),u)) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel u
        (tapeLeft (data::(payload ++ marked::L)) R) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program width) (0,t)
    (0,tapeLeft (data::(payload ++ marked::L)) R) rfl ht (2*width+2)
  rw [peek width data marked payload L R hlen] at h
  cases hr : run (program width) (0,t) (2*width+2) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hr] at h; exact False.elim h
    | inr d =>
      rcases d with ⟨q,u⟩
      rw [hr] at h
      change q = state (2*width+2) (flag marked) ∧ _ at h
      refine ⟨u,?_,h.2⟩
      simpa [h.1] using hr

end Shared.Codes.FiniteProgramProtectedMarkerPeek

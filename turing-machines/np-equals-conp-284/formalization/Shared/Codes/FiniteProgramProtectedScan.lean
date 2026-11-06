import Shared.Codes.FiniteProgramTwoWordClassify
import Shared.ComplexityBridge.PairReverseWitness

/-! A finite binary-table scanner for a protected output block, read from
right to left. It retains the data and marker bits in four continuation states
and requires the occupied bit to be true. It does not compact the output. -/
namespace Shared.Codes.FiniteProgramProtectedScan
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTwoWordClassify (mask first second)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def state (i : Nat) (m : Fin 4) : Nat := 4*i+m.val

def update (width i : Nat) (m : Fin 4) (read : Bool) : Fin 4 :=
  if i = 0 then mask read false
  else if i = width+1 then mask (first m) read
  else m

def liveRow (width i : Nat) (m : Fin 4) (read : Bool) : Row :=
  if i = width+2 ∧ read = false then (read,false,0,1)
  else (read,false,state (i+1) (update width i m read),0)

def terminalRow (read : Bool) : Row := (read,false,0,1)

def rowPair (width : Nat) (q : Fin (4*(width+4))) : Row × Row :=
  let i := q.val / 4
  let m : Fin 4 := ⟨q.val % 4,by omega⟩
  if i < width+3 then (liveRow width i m false,liveRow width i m true)
  else (terminalRow false,terminalRow true)

def program (width : Nat) : Program := List.ofFn (rowPair width)

@[simp] theorem program_length (width : Nat) : (program width).length = 4*(width+4) := by
  simp [program]
  omega

theorem state_bound (width i : Nat) (m : Fin 4) (hi : i ≤ width+3) :
    state i m < (program width).length := by
  have hm := m.isLt
  simp only [program_length,state]
  omega

/-- The data bit and marker are both recoverable from the continuation state. -/
theorem state_pair_injective (i : Nat) :
    Function.Injective (fun x : Bool × Bool => state i (mask x.1 x.2)) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  cases a <;> cases b <;> cases c <;> cases d <;> simp [state,mask] at h ⊢ <;> omega

theorem row_at (width i : Nat) (m : Fin 4) (hi : i ≤ width+3) :
    (program width)[state i m]? = some (if i < width+3 then
      (liveRow width i m false,liveRow width i m true)
      else (terminalRow false,terminalRow true)) := by
  have hb := state_bound width i m hi
  rw [List.getElem?_eq_getElem hb]
  simp only [program,List.getElem_ofFn,rowPair]
  have hd : (4*i+m.val)/4 = i := by have hm := m.isLt; omega
  have hm : (4*i+m.val)%4 = m.val := by have h := m.isLt; omega
  simp [state,hd,hm]

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
    simp only [program_length,rowPair]
    split
    · have hi : q.val / 4 < width+3 := by assumption
      have hb : ∀ m : Fin 4, state (q.val/4+1) m < 4*(width+4) := by
        intro m; have hm := m.isLt; simp only [state]; omega
      by_cases he : q.val / 4 = width+2
      · have hb' : ∀ m : Fin 4, state (width+2+1) m < 4*(width+4) := by
          intro m
          rw [← he]
          exact hb m
        simp [liveRow,validRow,he,hb']
      · simp [liveRow,validRow,he,hb]
    · simp [terminalRow,validRow]
  change (!(program width).isEmpty && (program width).all
    (fun r => validRow (program width).length r.1 && validRow (program width).length r.2)) = true
  rw [hn,hall]
  rfl

/-- A live scan reads one bit and moves left, unless the occupied-bit check
finds false. -/
theorem step_live (width i : Nat) (m : Fin 4) (bit : Bool)
    (hi : i < width+3) (hok : i ≠ width+2 ∨ bit = true) (L R : List Bool) :
    step (program width) (state i m,tapeLeft (bit::L) R) =
      some (.inr (state (i+1) (update width i m bit),tapeLeft L (bit::R))) := by
  have hr := row_at width i m (by omega)
  simp only [hi,if_true] at hr
  cases bit <;> simp_all [step,liveRow,tapeLeft,moveTape]

/-- An unset occupied flag is rejected at the occupied-bit check. -/
theorem step_unoccupied (width : Nat) (m : Fin 4) (L R : List Bool) :
    step (program width) (state (width+2) m,tapeLeft (false::L) R) = some (.inl false) := by
  have hr := row_at width (width+2) m (by omega)
  simp only [show width+2 < width+3 by omega,if_true] at hr
  simp [step,hr,liveRow,tapeLeft]

/-- The four final states are placeholders for the future compaction step. -/
theorem terminal_placeholder (width : Nat) (m : Fin 4) (t : Tape) :
    step (program width) (state (width+3) m,t) = some (.inl false) := by
  have hr := row_at width (width+3) m (by omega)
  simp only [lt_self_iff_false,if_false] at hr
  cases ht : t.2.1 <;> simp [step,hr,terminalRow,ht]

/-- Interior payload cells are traversed without changing the stored data
bit or marker bit. -/
theorem skip_payload (width i : Nat) (m : Fin 4) (xs L R : List Bool)
    (hpos : 1 ≤ i) (hbound : i+xs.length ≤ width+1) :
    run (program width) (state i m,tapeLeft (xs++L) R) xs.length =
      some (.inr (state (i+xs.length) m,tapeLeft L (xs.reverse++R))) := by
  induction xs generalizing i R with
  | nil => simp [run]
  | cons x xs ih =>
    have hi : i < width+3 := by simp only [List.length_cons] at hbound; omega
    have hc : i ≠ width+2 := by simp only [List.length_cons] at hbound; omega
    have hne0 : i ≠ 0 := by omega
    have hnem : i ≠ width+1 := by simp only [List.length_cons] at hbound; omega
    have hstep := step_live width i m x hi (Or.inl hc) (xs++L) R
    have hrun : run (program width) (state i m,tapeLeft ((x::xs)++L) R) 1 =
        some (.inr (state (i+1) m,tapeLeft (xs++L) (x::R))) := by
      simpa [run,advance,update,hne0,hnem] using hstep
    have htail := ih (i+1) (x::R) (by omega) (by simp only [List.length_cons] at hbound; omega)
    rw [show (x::xs).length = 1+xs.length by simp [Nat.add_comm],run_continue _ _ _ 1 _ hrun]
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail

/-- Starting on the written data bit, the table scans a complete protected
block in exactly `width+3` transitions, preserving the tape and recording the
data/marker pair in the final state. -/
theorem scan_block (width : Nat) (b marked : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) :
    run (program width) (0,tapeLeft (b::(payload ++ [marked,true]) ++ L) R) (width+3) =
      some (.inr (state (width+3) (mask b marked),
        tapeLeft L (true::marked::(payload.reverse ++ b::R)))) := by
  have hfirst := step_live width 0 (mask true true) b (by omega) (Or.inl (by omega))
    (payload ++ [marked,true] ++ L) R
  have hr1 : run (program width) (0,tapeLeft (b::(payload ++ [marked,true]) ++ L) R) 1 =
      some (.inr (state 1 (mask b false),tapeLeft (payload ++ [marked,true] ++ L) (b::R))) := by
    simpa [run,advance,state,mask,update,List.append_assoc] using hfirst
  have hp := skip_payload width 1 (mask b false) payload (marked::true::L) (b::R)
    (by omega) (by simp [hlen]; omega)
  have hp' : run (program width)
      (state 1 (mask b false),tapeLeft (payload ++ [marked,true] ++ L) (b::R)) width =
      some (.inr (state (width+1) (mask b false),
        tapeLeft (marked::true::L) (payload.reverse ++ b::R))) := by
    simpa [hlen,List.append_assoc,Nat.add_comm] using hp
  have hm := step_live width (width+1) (mask b false) marked (by omega) (Or.inl (by omega))
    (true::L) (payload.reverse ++ b::R)
  have hm' : run (program width)
      (state (width+1) (mask b false),tapeLeft (marked::true::L) (payload.reverse ++ b::R)) 1 =
      some (.inr (state (width+2) (mask b marked),
        tapeLeft (true::L) (marked::(payload.reverse ++ b::R)))) := by
    cases b <;> cases marked <;> simpa [run,advance,update,mask,first] using hm
  have ho := step_live width (width+2) (mask b marked) true (by omega) (Or.inr rfl)
    L (marked::(payload.reverse ++ b::R))
  have ho' : run (program width)
      (state (width+2) (mask b marked),tapeLeft (true::L) (marked::(payload.reverse ++ b::R))) 1 =
      some (.inr (state (width+3) (mask b marked),
        tapeLeft L (true::marked::(payload.reverse ++ b::R)))) := by
    simpa [run,advance,update] using ho
  rw [show width+3 = 1+(width+(1+1)) by omega,run_continue _ _ _ _ _ hr1,
    run_continue _ _ _ _ _ hp',run_continue _ _ _ _ _ hm']
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ho'

end Shared.Codes.FiniteProgramProtectedScan

import Shared.Codes.FiniteProgramWordCompare

/-! A single finite-table pass compares a tape word with two fixed words.
The four terminal control states retain both comparison results. -/
namespace Shared.Codes.FiniteProgramTwoWordClassify
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed consumed_cons)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def mask (a b : Bool) : Fin 4 :=
  if a then if b then ⟨0,by decide⟩ else ⟨1,by decide⟩
  else if b then ⟨2,by decide⟩ else ⟨3,by decide⟩

def first (m : Fin 4) : Bool := decide (m.val < 2)
def second (m : Fin 4) : Bool := m.val % 2 == 0

@[simp] theorem first_mask (a b : Bool) : first (mask a b) = a := by cases a <;> cases b <;> rfl
@[simp] theorem second_mask (a b : Bool) : second (mask a b) = b := by cases a <;> cases b <;> rfl

def state (i : Nat) (m : Fin 4) : Nat := 4*i+m.val

def liveRow (w₀ w₁ : List Bool) (i : Nat) (m : Fin 4) (read : Bool) : Row :=
  (read,true,state (i+1) (mask (first m && (read == w₀[i]!)) (second m && (read == w₁[i]!))),0)

def terminalRow (read : Bool) : Row := (read,true,0,1)

def rowPair (w₀ w₁ : List Bool) (q : Fin (4*(w₀.length+1))) : Row × Row :=
  let i := q.val / 4
  let m : Fin 4 := ⟨q.val % 4,by omega⟩
  if i < w₀.length then (liveRow w₀ w₁ i m false,liveRow w₀ w₁ i m true)
  else (terminalRow false,terminalRow true)

def program (w₀ w₁ : List Bool) : Program := List.ofFn (rowPair w₀ w₁)

@[simp] theorem program_length (w₀ w₁ : List Bool) :
    (program w₀ w₁).length = 4*(w₀.length+1) := by simp [program]; omega

theorem state_bound (w₀ w₁ : List Bool) (i : Nat) (m : Fin 4) (hi : i ≤ w₀.length) :
    state i m < (program w₀ w₁).length := by
  have hm := m.isLt
  simp only [program_length,state]
  omega

theorem row_at (w₀ w₁ : List Bool) (i : Nat) (m : Fin 4) (hi : i ≤ w₀.length) :
    (program w₀ w₁)[state i m]? = some (if i < w₀.length then
      (liveRow w₀ w₁ i m false,liveRow w₀ w₁ i m true)
      else (terminalRow false,terminalRow true)) := by
  have hb := state_bound w₀ w₁ i m hi
  rw [List.getElem?_eq_getElem hb]
  simp only [program,List.getElem_ofFn,rowPair]
  have hd : (4*i+m.val)/4 = i := by have hm := m.isLt; omega
  have hm : (4*i+m.val)%4 = m.val := by have hh := m.isLt; omega
  simp [state,hd,hm]

theorem step_live (w₀ w₁ : List Bool) (i : Nat) (m : Fin 4) (bit : Bool)
    (hi : i < w₀.length) (L R : List Bool) :
    step (program w₀ w₁) (state i m,tapeAt L (bit::R)) =
      some (.inr (state (i+1) (mask (first m && (bit == w₀[i]!))
        (second m && (bit == w₁[i]!))),tapeAt (bit::L) R)) := by
  have hr := row_at w₀ w₁ i m (by omega)
  simp only [hi,if_true] at hr
  cases bit <;> simp [step,hr,liveRow,tapeAt,moveTape]

theorem step_terminal (w₀ w₁ : List Bool) (m : Fin 4) (t : Tape) :
    step (program w₀ w₁) (state w₀.length m,t) = some (.inl false) := by
  have hr := row_at w₀ w₁ w₀.length m (by omega)
  simp only [lt_self_iff_false,if_false] at hr
  cases ht : t.2.1 <;> simp [step,hr,terminalRow,ht]

/-- The generated table is valid with four states per scan position. -/
theorem program_valid (w₀ w₁ : List Bool) : valid (program w₀ w₁) = true := by
  have hn : (program w₀ w₁).isEmpty = false := by
    cases h : program w₀ w₁ with
    | nil => have hl := program_length w₀ w₁; rw [h] at hl; simp at hl
    | cons r rs => rfl
  have hall : (program w₀ w₁).all
      (fun r => validRow (program w₀ w₁).length r.1 && validRow (program w₀ w₁).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    change r ∈ List.ofFn (rowPair w₀ w₁) at hr
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    simp only [program_length,rowPair]
    split
    · have hi : q.val / 4 < w₀.length := by assumption
      have hb : ∀ m : Fin 4, state (q.val/4+1) m < 4*(w₀.length+1) := by
        intro m; have hm := m.isLt; simp only [state]; omega
      simp [liveRow,validRow,hb]
    · simp [terminalRow,validRow]
  change (!(program w₀ w₁).isEmpty && (program w₀ w₁).all
    (fun r => validRow (program w₀ w₁).length r.1 && validRow (program w₀ w₁).length r.2)) = true
  rw [hn,hall]
  rfl

/-- Both equalities are tracked throughout the same scan. The table retains
the tape and takes exactly one transition per input bit. -/
theorem run_scan (w₀ w₁ pre rem₀ rem₁ observed suffix L : List Bool) (a b : Bool)
    (hw₀ : w₀ = pre ++ rem₀) (hwlen : w₀.length = w₁.length)
    (hi₁ : pre.length ≤ w₁.length) (hr₁ : rem₁ = w₁.drop pre.length)
    (hl₀ : observed.length = rem₀.length) (hl₁ : observed.length = rem₁.length) :
    run (program w₀ w₁) (state pre.length (mask a b),tapeAt L (observed++suffix)) observed.length =
      some (.inr (state w₀.length (mask (a && (observed == rem₀)) (b && (observed == rem₁))),
        tapeAt (consumed L observed) suffix)) := by
  induction rem₀ generalizing pre rem₁ observed L a b with
  | nil =>
    cases observed with
    | cons x xs => simp at hl₀
    | nil =>
      have he : rem₁ = [] := by cases rem₁ <;> simp_all
      subst rem₁
      simp [hw₀,consumed,he]
  | cons x xs ih =>
    cases observed with
    | nil => simp at hl₀
    | cons y ys =>
      cases rem₁ with
      | nil => simp at hl₁
      | cons z zs =>
        have hlen₀ : ys.length = xs.length := by simpa using hl₀
        have hlen₁ : ys.length = zs.length := by simpa using hl₁
        have hi : pre.length < w₀.length := by rw [hw₀]; simp
        have hi₁' : pre.length < w₁.length := by omega
        have hread₀ : w₀[pre.length]! = x := by simp [hw₀]
        have hread₁ : w₁[pre.length]! = z := by
          have h := congrArg List.head? hr₁
          simpa [List.head?_drop,hi₁'] using h.symm
        have hstep := step_live w₀ w₁ pre.length (mask a b) y hi L (ys++suffix)
        have hrun : run (program w₀ w₁) (state pre.length (mask a b),tapeAt L ((y::ys)++suffix)) 1 =
            some (.inr (state (pre.length+1) (mask (a && (y == x)) (b && (y == z))),
              tapeAt (y::L) (ys++suffix))) := by
          simpa [run,advance,hread₀,hread₁] using hstep
        have hnext₀ : w₀ = (pre++[x]) ++ xs := by simpa [List.append_assoc] using hw₀
        have hnext₁ : zs = w₁.drop (pre++[x]).length := by
          have h := congrArg List.tail hr₁
          simpa [List.drop_drop,Nat.add_comm] using h
        have ht := ih (pre++[x]) zs ys (y::L) (a && (y == x)) (b && (y == z))
          hnext₀ (by simp; omega) hnext₁ hlen₀ hlen₁
        rw [show (y::ys).length = 1+ys.length by simp [Nat.add_comm],run_continue _ _ _ 1 _ hrun]
        cases a <;> cases b <;> cases x <;> cases y <;> cases z <;>
          simpa [consumed_cons,List.append_assoc] using ht

/-- Scan once from state zero and retain both word-comparison results. -/
theorem classify_word (w₀ w₁ observed suffix L : List Bool)
    (hw : w₀.length = w₁.length) (ho : observed.length = w₀.length) :
    run (program w₀ w₁) (0,tapeAt L (observed++suffix)) w₀.length =
      some (.inr (state w₀.length (mask (observed == w₀) (observed == w₁)),
        tapeAt (consumed L observed) suffix)) := by
  have h := run_scan w₀ w₁ [] w₀ w₁ observed suffix L true true (by simp) hw
    (by simp) (by simp) (by simpa using ho) (by omega)
  simpa [state,mask,ho] using h

/-- Classification also works for any blank-equivalent tape representation. -/
theorem classify_word_related (w₀ w₁ observed suffix L : List Bool)
    (hw : w₀.length = w₁.length) (ho : observed.length = w₀.length) (t : Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t (tapeAt L (observed++suffix))) :
    ∃ t', run (program w₀ w₁) (0,t) w₀.length =
      some (.inr (state w₀.length (mask (observed == w₀) (observed == w₁)),t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (tapeAt (consumed L observed) suffix) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program w₀ w₁) (0,t)
    (0,tapeAt L (observed++suffix)) rfl ht w₀.length
  rw [classify_word w₀ w₁ observed suffix L hw ho] at h
  cases hr : run (program w₀ w₁) (0,t) w₀.length with
  | none => simp [Shared.Codes.FiniteProgramTapeEquiv.StatusRel,hr] at h
  | some v => cases v with
    | inl r => simp [Shared.Codes.FiniteProgramTapeEquiv.StatusRel,hr] at h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = state w₀.length (mask (observed == w₀) (observed == w₁)) ∧
        Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (tapeAt (consumed L observed) suffix) at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

end Shared.Codes.FiniteProgramTwoWordClassify

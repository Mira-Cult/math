import Shared.Codes.FiniteProgramThreeExit

/-! Replace two terminal rows by actual two-step writes into the immediately
preceding tape cell, then restart at state zero. Other terminal rows remain
available as exits. -/
namespace Shared.Codes.FiniteProgramWriteBackLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel move_related tape_head)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Turing

def goLeft (target : Nat) : Row × Row := ((false,false,target,0),(true,false,target,0))
def writeRight (value : Bool) : Row × Row := ((value,true,0,0),(value,true,0,0))

def program (p : Program) (a b : Nat) : Program :=
  (p.set a (goLeft p.length)).set b (goLeft (p.length+1)) ++ [writeRight false,writeRight true]

@[simp] theorem program_length (p : Program) (a b : Nat) : (program p a b).length = p.length+2 := by
  simp [program]

theorem source_other (p : Program) (a b : Nat) (d : Config) (hd : d.1 < p.length)
    (ha : d.1 ≠ a) (hb : d.1 ≠ b) : step p d = step (program p a b) d := by
  have h : (program p a b)[d.1]? = p[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb]
  simp [step,h]

theorem first_row (p : Program) (a b : Nat) (ha : a < p.length) (hab : a ≠ b) :
    (program p a b)[a]? = some (goLeft p.length) := by
  simp [program,List.getElem?_append_left,ha,Ne.symm hab]

theorem second_row (p : Program) (a b : Nat) (hb : b < p.length) :
    (program p a b)[b]? = some (goLeft (p.length+1)) := by
  simp [program,List.getElem?_append_left,hb]

theorem writer_rows (p : Program) (a b : Nat) :
    (program p a b)[p.length]? = some (writeRight false) ∧
    (program p a b)[p.length+1]? = some (writeRight true) := by simp [program]

/-- The resulting tape after the charged left-move and right-writing move. -/
def writePrevious (value : Bool) (t : Tape) : Tape :=
  moveTape false value (moveTape true t.2.1 t)

theorem writePrevious_related (value : Bool) (t u : Tape) (h : TapeRel t u) :
    TapeRel (writePrevious value t) (writePrevious value u) := by
  have hh := tape_head h
  have h₁ := move_related true t.2.1 t u h
  rw [hh] at h₁
  unfold writePrevious
  rw [hh]
  exact move_related false value _ _ h₁

theorem writePrevious_shape (value old : Bool) (L suffix : List Bool) :
    writePrevious value (tapeAt (old::L) suffix) = tapeAt (value::L) suffix := by
  cases suffix <;> rfl

theorem write_false (p : Program) (a b : Nat) (ha : a < p.length) (hab : a ≠ b) (t : Tape) :
    run (program p a b) (a,t) 2 = some (.inr (0,writePrevious false t)) := by
  have hr := first_row p a b ha hab
  have hw := (writer_rows p a b).1
  have h₁ : step (program p a b) (a,t) = some (.inr (p.length,moveTape true t.2.1 t)) := by
    cases ht : t.2.1 <;> simp only [step,hr,goLeft,ht] <;> rfl
  have h₂ (u : Tape) : step (program p a b) (p.length,u) = some (.inr (0,moveTape false false u)) := by
    cases hu : u.2.1 <;> simp only [step,hw,writeRight,hu] <;> rfl
  change advance (program p a b) (step (program p a b) (a,t)) = _
  rw [h₁]
  exact h₂ _

theorem write_true (p : Program) (a b : Nat) (hb : b < p.length) (t : Tape) :
    run (program p a b) (b,t) 2 = some (.inr (0,writePrevious true t)) := by
  have hr := second_row p a b hb
  have hw := (writer_rows p a b).2
  have h₁ : step (program p a b) (b,t) = some (.inr (p.length+1,moveTape true t.2.1 t)) := by
    cases ht : t.2.1 <;> simp only [step,hr,goLeft,ht] <;> rfl
  have h₂ (u : Tape) : step (program p a b) (p.length+1,u) = some (.inr (0,moveTape false true u)) := by
    cases hu : u.2.1 <;> simp only [step,hw,writeRight,hu] <;> rfl
  change advance (program p a b) (step (program p a b) (b,t)) = _
  rw [h₁]
  exact h₂ _

theorem first_entry (p : Program) (a b : Nat) (start last : Config) (n : Nat)
    (hp : valid p = true) (hstart : start.1 < p.length)
    (ha : ∃ r, ∀ t, step p (a,t) = some (.inl r))
    (hb : ∃ r, ∀ t, step p (b,t) = some (.inl r))
    (hr : run p start n = some (.inr last)) : run (program p a b) start n = some (.inr last) := by
  let stops : Set Nat := {a,b}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many p (program p a b)
    start last n stops hp hstart ?_ ?_ hr
  · intro s hs
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ha
    · exact hb
  · intro d hd hn
    have ha' : d.1 ≠ a := by intro h; apply hn; simp [stops,h]
    have hb' : d.1 ≠ b := by intro h; apply hn; simp [stops,h]
    exact source_other p a b d hd ha' hb'

theorem program_valid (p : Program) (a b : Nat) (hp : valid p = true) : valid (program p a b) = true := by
  let m := p.length+2
  have hpRows : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    have hv := hp
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    intro r hr
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hm : p.length ≤ m := by simp [m]
  have hleft (j : Nat) (hj : j < 2) :
      validRow m (goLeft (p.length+j)).1 = true ∧ validRow m (goLeft (p.length+j)).2 = true := by
    have hlt : p.length+j < m := by dsimp [m]; omega
    simp [goLeft,validRow,hlt]
  have hprefix : ((p.set a (goLeft p.length)).set b (goLeft (p.length+1))).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with hr | hr
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · obtain ⟨h₁,h₂⟩ := hpRows r hr
        have h₁' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₁
        have h₂' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₂
        simpa only [Bool.and_eq_true] using And.intro h₁' h₂'
      · subst r; simpa only [Bool.and_eq_true,Nat.add_zero] using hleft 0 (by omega)
    · subst r; simpa only [Bool.and_eq_true] using hleft 1 (by omega)
  have hrest : ([writeRight false,writeRight true] : Program).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    have hpos : 0 < m := by dsimp [m]; omega
    simp [writeRight,validRow,hpos]
  have hall : (program p a b).all
      (fun r => validRow (program p a b).length r.1 && validRow (program p a b).length r.2) = true := by
    rw [program_length]
    change (program p a b).all (fun r => validRow m r.1 && validRow m r.2) = true
    simp only [program,List.all_append,hprefix,hrest,Bool.and_self]
  have hn : (program p a b).isEmpty = false := by
    cases h : program p a b with
    | nil => have hl := program_length p a b; rw [h] at hl; simp at hl
    | cons r rs => rfl
  change (!(program p a b).isEmpty && (program p a b).all
    (fun r => validRow (program p a b).length r.1 && validRow (program p a b).length r.2)) = true
  rw [hn,hall]
  rfl

end Shared.Codes.FiniteProgramWriteBackLoop

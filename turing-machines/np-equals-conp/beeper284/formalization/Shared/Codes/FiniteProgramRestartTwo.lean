import Shared.Codes.FiniteProgramThreeExit

/-! Redirect two terminal rows to state zero using two charged moves. The
bounce preserves the tape modulo blank padding; all other source rows retain
their original behavior. -/
namespace Shared.Codes.FiniteProgramRestartTwo
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramThreeExit (bounce)

def program (p : Program) (a b : Nat) : Program :=
  (p.set a (branch p.length)).set b (branch (p.length+1)) ++ [bridge 0,bridge 0]

@[simp] theorem program_length (p : Program) (a b : Nat) : (program p a b).length = p.length+2 := by
  simp [program]

theorem source_other (p : Program) (a b : Nat) (d : Config) (hd : d.1 < p.length)
    (ha : d.1 ≠ a) (hb : d.1 ≠ b) : step p d = step (program p a b) d := by
  have h : (program p a b)[d.1]? = p[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb]
  simp [step,h]

theorem first_row (p : Program) (a b : Nat) (ha : a < p.length) (hab : a ≠ b) :
    (program p a b)[a]? = some (branch p.length) := by
  simp [program,List.getElem?_append_left,ha,Ne.symm hab]

theorem second_row (p : Program) (a b : Nat) (hb : b < p.length) :
    (program p a b)[b]? = some (branch (p.length+1)) := by
  simp [program,List.getElem?_append_left,hb]

theorem bridge_rows (p : Program) (a b : Nat) :
    (program p a b)[p.length]? = some (bridge 0) ∧
    (program p a b)[p.length+1]? = some (bridge 0) := by simp [program]

/-- The false/first branch returns to state zero after two physical steps. -/
theorem restart_first (p : Program) (a b : Nat) (ha : a < p.length) (hab : a ≠ b) (t : Tape) :
    run (program p a b) (a,t) 2 = some (.inr (0,bounce t)) := by
  have hr := first_row p a b ha hab
  have hb := (bridge_rows p a b).1
  have h₁ : step (program p a b) (a,t) = some (.inr (p.length,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,hr,branch,ht]
  have h₂ (u : Tape) : step (program p a b) (p.length,u) = some (.inr (0,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hb,bridge,hu] <;> rfl
  change advance (program p a b) (step (program p a b) (a,t)) = _
  rw [h₁]
  exact h₂ _

/-- The true/second branch has the same charged restart. -/
theorem restart_second (p : Program) (a b : Nat) (hb : b < p.length) (t : Tape) :
    run (program p a b) (b,t) 2 = some (.inr (0,bounce t)) := by
  have hr := second_row p a b hb
  have hbridge := (bridge_rows p a b).2
  have h₁ : step (program p a b) (b,t) = some (.inr (p.length+1,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,hr,branch,ht]
  have h₂ (u : Tape) : step (program p a b) (p.length+1,u) = some (.inr (0,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hbridge,bridge,hu] <;> rfl
  change advance (program p a b) (step (program p a b) (b,t)) = _
  rw [h₁]
  exact h₂ _

/-- A source run reaching a live configuration is preserved through its first
entry into either replaced terminal row. -/
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

/-- The two restart bridges add exactly two valid states. -/
theorem program_valid (p : Program) (a b : Nat) (hp : valid p = true) : valid (program p a b) = true := by
  let m := p.length+2
  have hpRows : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    have hv := hp
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    intro r hr
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hm : p.length ≤ m := by simp [m]
  have hbranch (j : Nat) (hj : j < 2) :
      validRow m (branch (p.length+j)).1 = true ∧ validRow m (branch (p.length+j)).2 = true := by
    have hlt : p.length+j < m := by dsimp [m]; omega
    simp [branch,validRow,hlt]
  have hprefix : ((p.set a (branch p.length)).set b (branch (p.length+1))).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with hr | hr
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · obtain ⟨h₁,h₂⟩ := hpRows r hr
        have h₁' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₁
        have h₂' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₂
        simpa only [Bool.and_eq_true] using And.intro h₁' h₂'
      · subst r; simpa only [Bool.and_eq_true,Nat.add_zero] using hbranch 0 (by omega)
    · subst r; simpa only [Bool.and_eq_true] using hbranch 1 (by omega)
  have hrest : ([bridge 0,bridge 0] : Program).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    have hpos : 0 < m := by dsimp [m]; omega
    simp [bridge,validRow,hpos]
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

end Shared.Codes.FiniteProgramRestartTwo

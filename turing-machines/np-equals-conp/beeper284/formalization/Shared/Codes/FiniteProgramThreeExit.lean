import Shared.Codes.FiniteProgramFirstEntryMany
import Shared.Codes.FiniteProgramExtendAdvance

/-! Redirect three terminal rows to distinct live continuation rows. Each
handoff takes two actual transitions and preserves the tape modulo blanks.
The final continuation rows are explicit placeholders for later linking. -/
namespace Shared.Codes.FiniteProgramThreeExit
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.TM0FiniteProgram (tape tape_move run_continue)
open Turing

def stop : Row × Row := ((false,true,0,1),(true,true,0,1))

def program (p : Program) (a b c : Nat) : Program :=
  ((p.set a (branch p.length)).set b (branch (p.length+1))).set c (branch (p.length+2)) ++
    [bridge (p.length+3),bridge (p.length+4),bridge (p.length+5),stop,stop,stop]

@[simp] theorem program_length (p : Program) (a b c : Nat) :
    (program p a b c).length = p.length+6 := by simp [program]

theorem source_other (p : Program) (a b c : Nat) (d : Config) (hd : d.1 < p.length)
    (ha : d.1 ≠ a) (hb : d.1 ≠ b) (hc : d.1 ≠ c) :
    step p d = step (program p a b c) d := by
  have h : (program p a b c)[d.1]? = p[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb,Ne.symm hc]
  simp [step,h]

theorem first_row (p : Program) (a b c : Nat) (ha : a < p.length) (hab : a ≠ b) (hac : a ≠ c) :
    (program p a b c)[a]? = some (branch p.length) := by
  simp [program,List.getElem?_append_left,ha,Ne.symm hab,Ne.symm hac]

theorem second_row (p : Program) (a b c : Nat) (hb : b < p.length) (hbc : b ≠ c) :
    (program p a b c)[b]? = some (branch (p.length+1)) := by
  simp [program,List.getElem?_append_left,hb,Ne.symm hbc]

theorem third_row (p : Program) (a b c : Nat) (hc : c < p.length) :
    (program p a b c)[c]? = some (branch (p.length+2)) := by
  simp [program,List.getElem?_append_left,hc]

theorem bridge_rows (p : Program) (a b c : Nat) :
    (program p a b c)[p.length]? = some (bridge (p.length+3)) ∧
    (program p a b c)[p.length+1]? = some (bridge (p.length+4)) ∧
    (program p a b c)[p.length+2]? = some (bridge (p.length+5)) := by
  simp [program]

theorem continuation_rows (p : Program) (a b c : Nat) :
    (program p a b c)[p.length+3]? = some stop ∧
    (program p a b c)[p.length+4]? = some stop ∧
    (program p a b c)[p.length+5]? = some stop := by
  simp [program]

/-- Move right and immediately left, rewriting each visited bit to itself. -/
def bounce (t : Tape) : Tape :=
  let u := moveTape false t.2.1 t
  moveTape true u.2.1 u

theorem bounce_related (t : Tape) : TapeRel (bounce t) t := by
  let u := moveTape false t.2.1 t
  have h₁ := tape_move t t.2.1 Dir.right
  change tape u = ((tape t).write (tape t).head).move .right at h₁
  rw [Tape.write_self] at h₁
  have h₂ := tape_move u u.2.1 Dir.left
  change tape (bounce t) = ((tape u).write (tape u).head).move .left at h₂
  rw [Tape.write_self,h₁,Tape.move_right_left] at h₂
  exact h₂

theorem handoff_first (p : Program) (a b c : Nat) (ha : a < p.length)
    (hab : a ≠ b) (hac : a ≠ c) (t : Tape) :
    run (program p a b c) (a,t) 2 = some (.inr (p.length+3,bounce t)) := by
  have h := first_row p a b c ha hab hac
  have hb := (bridge_rows p a b c).1
  have h₁ : step (program p a b c) (a,t) = some (.inr (p.length,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,h,branch,ht]
  have h₂ (u : Tape) : step (program p a b c) (p.length,u) =
      some (.inr (p.length+3,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hb,bridge,hu] <;> rfl
  change advance (program p a b c) (step (program p a b c) (a,t)) = _
  rw [h₁]
  exact h₂ _

theorem handoff_second (p : Program) (a b c : Nat) (hb : b < p.length)
    (hbc : b ≠ c) (t : Tape) :
    run (program p a b c) (b,t) 2 = some (.inr (p.length+4,bounce t)) := by
  have h := second_row p a b c hb hbc
  have hb' := (bridge_rows p a b c).2.1
  have h₁ : step (program p a b c) (b,t) = some (.inr (p.length+1,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,h,branch,ht]
  have h₂ (u : Tape) : step (program p a b c) (p.length+1,u) =
      some (.inr (p.length+4,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hb',bridge,hu] <;> rfl
  change advance (program p a b c) (step (program p a b c) (b,t)) = _
  rw [h₁]
  exact h₂ _

theorem handoff_third (p : Program) (a b c : Nat) (hc : c < p.length) (t : Tape) :
    run (program p a b c) (c,t) 2 = some (.inr (p.length+5,bounce t)) := by
  have h := third_row p a b c hc
  have hb := (bridge_rows p a b c).2.2
  have h₁ : step (program p a b c) (c,t) = some (.inr (p.length+2,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,h,branch,ht]
  have h₂ (u : Tape) : step (program p a b c) (p.length+2,u) =
      some (.inr (p.length+5,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hb,bridge,hu] <;> rfl
  change advance (program p a b c) (step (program p a b c) (c,t)) = _
  rw [h₁]
  exact h₂ _

/-- Any run ending in a live configuration is preserved before the three
terminal rows, regardless of their individual Boolean results. -/
theorem first_entry (p : Program) (a b c : Nat) (start last : Config) (n : Nat)
    (hp : valid p = true) (hstart : start.1 < p.length)
    (ha : ∃ r, ∀ t, step p (a,t) = some (.inl r))
    (hb : ∃ r, ∀ t, step p (b,t) = some (.inl r))
    (hc : ∃ r, ∀ t, step p (c,t) = some (.inl r))
    (hr : run p start n = some (.inr last)) :
    run (program p a b c) start n = some (.inr last) := by
  let stops : Set Nat := {a,b,c}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many p (program p a b c)
    start last n stops hp hstart ?_ ?_ hr
  · intro s hs
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · intro d hd hn
    have ha' : d.1 ≠ a := by intro h; apply hn; simp [stops,h]
    have hb' : d.1 ≠ b := by intro h; apply hn; simp [stops,h]
    have hc' : d.1 ≠ c := by intro h; apply hn; simp [stops,h]
    exact source_other p a b c d hd ha' hb' hc'

/-- The three routed exits and their explicit placeholder rows form a valid
finite table whenever the original table is valid. -/
theorem program_valid (p : Program) (a b c : Nat) (hp : valid p = true) :
    valid (program p a b c) = true := by
  let m := p.length+6
  have hpRows : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    have hv := hp
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    intro r hr
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hm : p.length ≤ m := by simp [m]
  have hbranch (j : Nat) (hj : j < 3) :
      validRow m (branch (p.length+j)).1 = true ∧ validRow m (branch (p.length+j)).2 = true := by
    have hlt : p.length+j < m := by dsimp [m]; omega
    simp [branch,validRow,hlt]
  have hprefix : (((p.set a (branch p.length)).set b (branch (p.length+1))).set c (branch (p.length+2))).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with hr | hr
    · rcases List.mem_or_eq_of_mem_set hr with hr | hr
      · rcases List.mem_or_eq_of_mem_set hr with hr | hr
        · obtain ⟨h₁,h₂⟩ := hpRows r hr
          have h₁' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₁
          have h₂' := Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm h₂
          simpa only [Bool.and_eq_true] using And.intro h₁' h₂'
        · subst r; simpa only [Bool.and_eq_true,Nat.add_zero] using hbranch 0 (by omega)
      · subst r; simpa only [Bool.and_eq_true] using hbranch 1 (by omega)
    · subst r; simpa only [Bool.and_eq_true] using hbranch 2 (by omega)
  have hrest : ([bridge (p.length+3),bridge (p.length+4),bridge (p.length+5),stop,stop,stop] : Program).all
      (fun r => validRow m r.1 && validRow m r.2) = true := by
    have h₃ : p.length+3 < m := by dsimp [m]; omega
    have h₄ : p.length+4 < m := by dsimp [m]; omega
    have h₅ : p.length+5 < m := by dsimp [m]; omega
    simp [bridge,stop,validRow,h₃,h₄,h₅]
  have hall : (program p a b c).all
      (fun r => validRow (program p a b c).length r.1 && validRow (program p a b c).length r.2) = true := by
    rw [program_length]
    change (program p a b c).all (fun r => validRow m r.1 && validRow m r.2) = true
    simp only [program,List.all_append,hprefix,hrest,Bool.and_self]
  have hn : (program p a b c).isEmpty = false := by
    cases h : program p a b c with
    | nil => have hl := program_length p a b c; rw [h] at hl; simp at hl
    | cons r rs => rfl
  change (!(program p a b c).isEmpty && (program p a b c).all
    (fun r => validRow (program p a b c).length r.1 && validRow (program p a b c).length r.2)) = true
  rw [hn,hall]
  rfl

end Shared.Codes.FiniteProgramThreeExit

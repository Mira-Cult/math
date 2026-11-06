import Shared.Codes.FiniteProgramTwoExit
import Shared.Codes.FiniteProgramThreeExit

/-! Redirect two terminal rows to relocated finite programs. With distinct,
in-range exits and nonempty continuations, both destinations are installed and
distinct. Each handoff costs two physical transitions and preserves the tape
modulo blank padding. The branch is retained in finite control, not on tape. -/
namespace Shared.Codes.FiniteProgramFork
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramThreeExit (bounce)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)

def pre (p q₀ : Program) (a b : Nat) : Program :=
  (p.set a (branch p.length)).set b (branch (p.length+1)) ++
    [bridge (p.length+2),bridge (p.length+2+q₀.length)]

def off₀ (p : Program) : Nat := p.length+2
def off₁ (p q₀ : Program) : Nat := off₀ p+q₀.length

def program (p q₀ q₁ : Program) (a b : Nat) : Program :=
  pre p q₀ a b ++ q₀.map (shiftPair (off₀ p)) ++ q₁.map (shiftPair (off₁ p q₀))

@[simp] theorem pre_length (p q₀ : Program) (a b : Nat) :
    (pre p q₀ a b).length = off₀ p := by simp [pre,off₀]

@[simp] theorem program_length (p q₀ q₁ : Program) (a b : Nat) :
    (program p q₀ q₁ a b).length = off₁ p q₀+q₁.length := by
  simp [program,off₁,Nat.add_assoc]

theorem source_other (p q₀ q₁ : Program) (a b : Nat) (d : Config)
    (hd : d.1 < p.length) (ha : d.1 ≠ a) (hb : d.1 ≠ b) :
    step p d = step (program p q₀ q₁ a b) d := by
  have hl : (program p q₀ q₁ a b)[d.1]? = p[d.1]? := by
    simp [program,pre,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb]
  simp [step,hl]

theorem first_entry (p q₀ q₁ : Program) (a b : Nat) (c d : Config) (n : Nat)
    (hp : valid p = true) (hc : c.1 < p.length)
    (ha : ∀ t, step p (a,t) = some (.inl false))
    (hb : ∀ t, step p (b,t) = some (.inl false))
    (hr : run p c n = some (.inr d)) : run (program p q₀ q₁ a b) c n = some (.inr d) := by
  let stops : Set Nat := {a,b}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many p (program p q₀ q₁ a b)
    c d n stops hp hc ?_ ?_ hr
  · intro s hs
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨false,ha⟩
    · exact ⟨false,hb⟩
  · intro d hd hn
    have ha' : d.1 ≠ a := by intro h; apply hn; simp [stops,h]
    have hb' : d.1 ≠ b := by intro h; apply hn; simp [stops,h]
    exact source_other p q₀ q₁ a b d hd ha' hb'

theorem first_row (p q₀ q₁ : Program) (a b : Nat) (ha : a < p.length) (hne : a ≠ b) :
    (program p q₀ q₁ a b)[a]? = some (branch p.length) := by
  simp [program,pre,List.getElem?_append_left,ha,Ne.symm hne]

theorem second_row (p q₀ q₁ : Program) (a b : Nat) (hb : b < p.length) :
    (program p q₀ q₁ a b)[b]? = some (branch (p.length+1)) := by
  simp [program,pre,List.getElem?_append_left,hb]

theorem bridges (p q₀ q₁ : Program) (a b : Nat) :
    (program p q₀ q₁ a b)[p.length]? = some (bridge (off₀ p)) ∧
    (program p q₀ q₁ a b)[p.length+1]? = some (bridge (off₁ p q₀)) := by
  simp [program,pre,off₀,off₁]

theorem handoff_first (p q₀ q₁ : Program) (a b : Nat) (ha : a < p.length)
    (hne : a ≠ b) (t : Tape) :
    run (program p q₀ q₁ a b) (a,t) 2 = some (.inr (off₀ p,bounce t)) := by
  have hr := first_row p q₀ q₁ a b ha hne
  have hb := (bridges p q₀ q₁ a b).1
  have h₁ : step (program p q₀ q₁ a b) (a,t) = some (.inr (p.length,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,hr,branch,ht]
  have h₂ (u : Tape) : step (program p q₀ q₁ a b) (p.length,u) =
      some (.inr (off₀ p,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hb,bridge,hu] <;> rfl
  change advance _ (step _ (a,t)) = _
  rw [h₁]
  exact h₂ _

theorem handoff_second (p q₀ q₁ : Program) (a b : Nat) (hb : b < p.length) (t : Tape) :
    run (program p q₀ q₁ a b) (b,t) 2 = some (.inr (off₁ p q₀,bounce t)) := by
  have hr := second_row p q₀ q₁ a b hb
  have hbridge := (bridges p q₀ q₁ a b).2
  have h₁ : step (program p q₀ q₁ a b) (b,t) = some (.inr (p.length+1,moveTape false t.2.1 t)) := by
    cases ht : t.2.1 <;> simp [step,hr,branch,ht]
  have h₂ (u : Tape) : step (program p q₀ q₁ a b) (p.length+1,u) =
      some (.inr (off₁ p q₀,moveTape true u.2.1 u)) := by
    cases hu : u.2.1 <;> simp only [step,hbridge,bridge,hu] <;> rfl
  change advance _ (step _ (b,t)) = _
  rw [h₁]
  exact h₂ _

theorem continuation_first (p q₀ q₁ : Program) (a b : Nat) (hq : valid q₀ = true)
    (c : Config) (hc : c.1 < q₀.length) (n : Nat) :
    run (program p q₀ q₁ a b) (shiftConfig (off₀ p) c) n =
      shiftStatus (off₀ p) (run q₀ c n) := by
  have h := run_shift (pre p q₀ a b) q₀ (q₁.map (shiftPair (off₁ p q₀))) hq c hc n
  simpa [program,link] using h

theorem continuation_second (p q₀ q₁ : Program) (a b : Nat) (hq : valid q₁ = true)
    (c : Config) (hc : c.1 < q₁.length) (n : Nat) :
    run (program p q₀ q₁ a b) (shiftConfig (off₁ p q₀) c) n =
      shiftStatus (off₁ p q₀) (run q₁ c n) := by
  let pre₁ := pre p q₀ a b ++ q₀.map (shiftPair (off₀ p))
  have hlen : pre₁.length = off₁ p q₀ := by simp [pre₁,off₁]
  have h := run_shift pre₁ q₁ [] hq c hc n
  simpa [program,link,pre₁,hlen] using h

/-- Validity of all three tables ensures the forked finite table is valid. -/
theorem program_valid (p q₀ q₁ : Program) (a b : Nat)
    (hp : valid p = true) (h₀ : valid q₀ = true) (h₁ : valid q₁ = true) :
    valid (program p q₀ q₁ a b) = true := by
  let m := off₁ p q₀+q₁.length
  have hq0pos := Shared.Codes.FiniteProgramLink.valid_nonempty q₀ h₀
  have hq1pos := Shared.Codes.FiniteProgramLink.valid_nonempty q₁ h₁
  have hl : (program p q₀ q₁ a b).length = m := program_length p q₀ q₁ a b
  have rows (q : Program) (hq : valid q = true) :
      ∀ r ∈ q, validRow q.length r.1 = true ∧ validRow q.length r.2 = true := by
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hq
    intro r hr
    simpa only [Bool.and_eq_true] using hq.2 r hr
  have hp_m : p.length ≤ m := by dsimp [m,off₁,off₀]; omega
  have hbound₀ : off₀ p < m := by dsimp [m,off₁]; omega
  have hbound₁ : off₁ p q₀ < m := by dsimp [m]; omega
  have hb0 : validRow m (branch p.length).1 = true ∧ validRow m (branch p.length).2 = true := by
    have h : p.length < m := by dsimp [m,off₁,off₀]; omega
    simp [branch,validRow,h]
  have hb1 : validRow m (branch (p.length+1)).1 = true ∧ validRow m (branch (p.length+1)).2 = true := by
    have h : p.length+1 < m := by dsimp [m,off₁,off₀]; omega
    simp [branch,validRow,h]
  have ht0 : validRow m (bridge (off₀ p)).1 = true ∧ validRow m (bridge (off₀ p)).2 = true := by
    simp [bridge,validRow,hbound₀]
  have ht1 : validRow m (bridge (off₁ p q₀)).1 = true ∧ validRow m (bridge (off₁ p q₀)).2 = true := by
    simp [bridge,validRow,hbound₁]
  have hpre : ∀ r ∈ pre p q₀ a b, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hr' : r ∈ (p.set a (branch p.length)).set b (branch (p.length+1)) ∨
        r = bridge (off₀ p) ∨ r = bridge (off₁ p q₀) := by
      simpa [pre,off₀,off₁] using hr
    rcases hr' with hr | rfl | rfl
    · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
      · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
        · obtain ⟨h₁,h₂⟩ := rows p hp r hr
          exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₁,
            Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₂⟩
        · exact hb0
      · exact hb1
    · exact ht0
    · exact ht1
  have hall : (program p q₀ q₁ a b).all
      (fun r => validRow (program p q₀ q₁ a b).length r.1 && validRow (program p q₀ q₁ a b).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre p q₀ a b ∨ r ∈ q₀.map (shiftPair (off₀ p)) ∨
        r ∈ q₁.map (shiftPair (off₁ p q₀)) := by simpa [program,List.mem_append] using hr
    rw [hl]
    rcases hr' with hp' | h0' | h1'
    · simpa only [Bool.and_eq_true] using hpre r hp'
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp h0'
      obtain ⟨ha,hb⟩ := rows q₀ h₀ r' hr'
      have hle : off₀ p+q₀.length ≤ m := by dsimp [m,off₁]; omega
      have ha' := Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 (off₀ p) q₀.length ha
      have hb' := Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 (off₀ p) q₀.length hb
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle ha',
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle hb'⟩
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp h1'
      obtain ⟨ha,hb⟩ := rows q₁ h₁ r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 (off₁ p q₀) q₁.length ha,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 (off₁ p q₀) q₁.length hb⟩
  have hne : (program p q₀ q₁ a b).isEmpty = false := by
    cases h : program p q₀ q₁ a b with
    | nil => simp [h] at hl; dsimp [m,off₁,off₀] at hl; omega
    | cons r rs => rfl
  change (!(program p q₀ q₁ a b).isEmpty && (program p q₀ q₁ a b).all
    (fun r => validRow (program p q₀ q₁ a b).length r.1 && validRow (program p q₀ q₁ a b).length r.2)) = true
  rw [hne,hall]
  rfl

end Shared.Codes.FiniteProgramFork

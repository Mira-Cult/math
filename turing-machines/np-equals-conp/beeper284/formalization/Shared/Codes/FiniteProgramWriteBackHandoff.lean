import Shared.Codes.FiniteProgramWriteBackLoop
import Shared.Codes.FiniteProgramTaggedExtend

/-! Replace two source terminal rows by charged writes and transfer control to
an appended finite continuation. Unlike the cyclic writer, this executes the
source pass once and reaches the continuation offset. When the continuation
is valid, that offset is its relocated state zero. -/
namespace Shared.Codes.FiniteProgramWriteBackHandoff
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramWriteBackLoop (goLeft writePrevious)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def writeTo (value : Bool) (next : Nat) : Row × Row :=
  ((value,true,next,0),(value,true,next,0))

def headPart (p : Program) (a b : Nat) : Program :=
  (p.set a (goLeft p.length)).set b (goLeft (p.length+1)) ++
    [writeTo false (p.length+2),writeTo true (p.length+2)]

def program (p : Program) (a b : Nat) (q : Program) : Program := link (headPart p a b) q []

@[simp] theorem prefix_length (p : Program) (a b : Nat) : (headPart p a b).length = p.length+2 := by
  simp [headPart]

@[simp] theorem program_length (p : Program) (a b : Nat) (q : Program) :
    (program p a b q).length = p.length+2+q.length := by simp [program,link]

theorem source_other (p : Program) (a b : Nat) (q : Program) (d : Config) (hd : d.1 < p.length)
    (ha : d.1 ≠ a) (hb : d.1 ≠ b) : step p d = step (program p a b q) d := by
  have h : (program p a b q)[d.1]? = p[d.1]? := by
    simp [program,link,headPart,List.getElem?_append_left,hd,Ne.symm ha,Ne.symm hb]
  simp [step,h]

theorem first_entry (p : Program) (a b : Nat) (q : Program) (start last : Config) (n : Nat)
    (hp : valid p = true) (hstart : start.1 < p.length)
    (ha : ∃ r, ∀ t, step p (a,t) = some (.inl r))
    (hb : ∃ r, ∀ t, step p (b,t) = some (.inl r))
    (hr : run p start n = some (.inr last)) : run (program p a b q) start n = some (.inr last) := by
  let stops : Set Nat := {a,b}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many p (program p a b q)
    start last n stops hp hstart ?_ ?_ hr
  · intro s hs
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ha
    · exact hb
  · intro d hd hn
    have ha' : d.1 ≠ a := by intro h; apply hn; simp [stops,h]
    have hb' : d.1 ≠ b := by intro h; apply hn; simp [stops,h]
    exact source_other p a b q d hd ha' hb'

theorem handoff (p : Program) (a b : Nat) (q : Program) (v : Bool) (t : Tape)
    (ha : a < p.length) (hb : b < p.length) (hab : a ≠ b) :
    run (program p a b q) (if v then b else a,t) 2 =
      some (.inr ((headPart p a b).length,writePrevious v t)) := by
  have hzero : (program p a b q)[a]? = some (goLeft p.length) := by
    simp [program,link,headPart,List.getElem?_append_left,ha,Ne.symm hab]
  have hone : (program p a b q)[b]? = some (goLeft (p.length+1)) := by
    simp [program,link,headPart,List.getElem?_append_left,hb]
  have hwzero : (program p a b q)[p.length]? = some (writeTo false (p.length+2)) := by
    simp [program,link,headPart]
  have hwone : (program p a b q)[p.length+1]? = some (writeTo true (p.length+2)) := by
    simp [program,link,headPart]
  cases v with
  | false =>
    have h₁ : step (program p a b q) (a,t) = some (.inr (p.length,moveTape true t.2.1 t)) := by
      cases ht : t.2.1 <;> simp only [step,hzero,goLeft,ht] <;> rfl
    have h₂ (u : Tape) : step (program p a b q) (p.length,u) =
        some (.inr (p.length+2,moveTape false false u)) := by
      cases hu : u.2.1 <;> simp only [step,hwzero,writeTo,hu] <;> rfl
    change advance _ (step _ (a,t)) = _
    rw [h₁]
    simpa [writePrevious,advance] using h₂ _
  | true =>
    have h₁ : step (program p a b q) (b,t) = some (.inr (p.length+1,moveTape true t.2.1 t)) := by
      cases ht : t.2.1 <;> simp only [step,hone,goLeft,ht] <;> rfl
    have h₂ (u : Tape) : step (program p a b q) (p.length+1,u) =
        some (.inr (p.length+2,moveTape false true u)) := by
      cases hu : u.2.1 <;> simp only [step,hwone,writeTo,hu] <;> rfl
    change advance _ (step _ (b,t)) = _
    rw [h₁]
    simpa [writePrevious,advance] using h₂ _

/-- The continuation is relocated behind the headPart, without changing time. -/
theorem continuation (p : Program) (a b : Nat) (q : Program) (hq : valid q = true)
    (c : Config) (hc : c.1 < q.length) (n : Nat) :
    run (program p a b q) (shiftConfig (headPart p a b).length c) n =
      shiftStatus (headPart p a b).length (run q c n) := by
  exact run_shift (headPart p a b) q [] hq c hc n

/-- Source and continuation validity ensure every installed state destination
is in range; the continuation must be nonempty. -/
theorem program_valid (p : Program) (a b : Nat) (q : Program)
    (hp : valid p = true) (hq : valid q = true) : valid (program p a b q) = true := by
  let m := (program p a b q).length
  have hqpos : 0 < q.length := Shared.Codes.FiniteProgramLink.valid_nonempty q hq
  have hm : m = p.length+2+q.length := by simp [m]
  have hpRows : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    have hv := hp
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    intro r hr
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hqRows : ∀ r ∈ q, validRow q.length r.1 = true ∧ validRow q.length r.2 = true := by
    have hv := hq
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    intro r hr
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hprefix : ∀ r ∈ headPart p a b,
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hr' : r ∈ (p.set a (goLeft p.length)).set b (goLeft (p.length+1)) ∨
        r = writeTo false (p.length+2) ∨ r = writeTo true (p.length+2) := by
      simpa [headPart] using hr
    rcases hr' with hr | rfl | rfl
    · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
      · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
        · obtain ⟨h₁,h₂⟩ := hpRows r hr
          have hle : p.length ≤ m := by omega
          exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle h₁,
            Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hle h₂⟩
        · have hlt : p.length < m := by omega
          simp [goLeft,validRow,hlt]
      · have hlt : p.length+1 < m := by omega
        simp [goLeft,validRow,hlt]
    · have hlt : p.length+2 < m := by omega
      simp [writeTo,validRow,hlt]
    · have hlt : p.length+2 < m := by omega
      simp [writeTo,validRow,hlt]
  have hall : (program p a b q).all
      (fun r => validRow (program p a b q).length r.1 && validRow (program p a b q).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ headPart p a b ∨ r ∈ q.map (shiftPair (headPart p a b).length) := by
      simpa [program,link,List.mem_append] using hr
    change (validRow m r.1 && validRow m r.2) = true
    rcases hr' with hr | hr
    · simpa only [Bool.and_eq_true] using hprefix r hr
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
      obtain ⟨h₁,h₂⟩ := hqRows r' hr'
      have hm' : m = (headPart p a b).length+q.length := by simp [hm]
      rw [hm']
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 _ _ h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 _ _ h₂⟩
  have hn : (program p a b q).isEmpty = false := by
    cases h : program p a b q with
    | nil =>
      have hlen := program_length p a b q
      rw [h] at hlen
      simp only [List.length_nil] at hlen
      omega
    | cons r rs => rfl
  change (!(program p a b q).isEmpty && (program p a b q).all
    (fun r => validRow (program p a b q).length r.1 && validRow (program p a b q).length r.2)) = true
  rw [hn,hall]
  rfl

end Shared.Codes.FiniteProgramWriteBackHandoff

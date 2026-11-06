import Shared.Codes.FiniteProgramFirstEntry
import Shared.Codes.FiniteProgramTaggedExtend

/-! Replace a finite program's final row by the relocated rows of a second
program. Correctness is conditional on the first program reaching that row;
there is no uncharged jump or termination assumption. -/
namespace Shared.Codes.FiniteProgramSplice
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift valid_nonempty)
open Shared.Codes.FiniteProgramTaggedExtend (shifted_valid)
open Shared.Codes.FiniteProgramShuttleSelect (validRow_mono)

def stem (p : Program) : Program := p.take (p.length-1)
def program (p q : Program) : Program := link (stem p) q []

theorem stem_length (p : Program) : (stem p).length = p.length-1 := by simp [stem]

theorem length_ge (p q : Program) (hp : valid p = true) (hq : valid q = true) :
    p.length ≤ (program p q).length := by
  have hp' := valid_nonempty p hp
  have hq' := valid_nonempty q hq
  simp [program,link,stem_length]
  omega

/-- The original table and the splice agree on all rows before the terminal
row, independently of the data in the continuation. -/
theorem step_before (p q : Program) (d : Config) (hd : d.1 < p.length-1) :
    step p d = step (program p q) d := by
  have hl : d.1 < (stem p).length := by simpa [stem_length] using hd
  have he : (program p q)[d.1]? = p[d.1]? := by
    simp [program,link,List.getElem?_append_left,stem,hd]
  simp [step,he]

/-- Replacing a terminal final row preserves every run up to its first entry. -/
theorem first_run (p q : Program) (hvalid : valid p = true) (c last : Config) (n : Nat) (result : Bool)
    (hc : c.1 < p.length)
    (hstop : ∀ t, step p (p.length-1,t) = some (.inl result))
    (hfinal : run p c n = some (.inr last)) :
    run (program p q) c n = some (.inr last) := by
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry p (program p q) c last n (p.length-1) result
    hvalid hc hstop ?_ hfinal
  intro d hd hne
  apply step_before p q d
  omega

/-- The second program starts at the removed row's index, and each of its
steps is charged exactly once. -/
theorem second_run (p q : Program) (hvalid : valid q = true) (c : Config)
    (hc : c.1 < q.length) (n : Nat) :
    run (program p q) (shiftConfig (p.length-1) c) n =
      shiftStatus (p.length-1) (run q c n) := by
  simpa [program,stem_length] using run_shift (stem p) q [] hvalid c hc n

/-- The splice remains a valid finite table when both inputs are valid. -/
theorem program_valid (p q : Program) (hp : valid p = true) (hq : valid q = true) :
    valid (program p q) = true := by
  let m := (program p q).length
  have hpall : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := hp
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hqall : ∀ r ∈ q, validRow q.length r.1 = true ∧ validRow q.length r.2 = true := by
    intro r hr
    have hv := hq
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hlen : m = (stem p).length+q.length := by simp [m,program,link]
  have hge : p.length ≤ m := length_ge p q hp hq
  have hall : (program p q).all
      (fun r => validRow (program p q).length r.1 && validRow (program p q).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ stem p ∨ r ∈ q.map (shiftPair (stem p).length) := by
      simpa [program,link,List.mem_append] using hr
    change (validRow m r.1 && validRow m r.2) = true
    rcases hr' with hs | hqmem
    · have hrp : r ∈ p := List.take_subset _ _ hs
      obtain ⟨h₁,h₂⟩ := hpall r hrp
      simp only [Bool.and_eq_true]
      exact ⟨validRow_mono _ _ _ hge h₁,validRow_mono _ _ _ hge h₂⟩
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hqmem
      obtain ⟨h₁,h₂⟩ := hqall r' hr'
      rw [hlen]
      simp only [Bool.and_eq_true]
      exact ⟨shifted_valid r'.1 _ _ h₁,shifted_valid r'.2 _ _ h₂⟩
  have hn : (program p q).isEmpty = false := by
    cases h : program p q with
    | nil =>
      have hpos := valid_nonempty p hp
      have hm0 : m = 0 := by simp [m,h]
      omega
    | cons r rs => rfl
  change (!(program p q).isEmpty && (program p q).all
    (fun r => validRow (program p q).length r.1 && validRow (program p q).length r.2)) = true
  rw [hn,hall]
  rfl

end Shared.Codes.FiniteProgramSplice

import Shared.PNP.Record285.PythonControlRelocationRun

/-! Conditional transfer of a terminating candidate-decoder segment to the
reference copy. The explicit before-boundary hypothesis remains to be proved
for the candidate decoder's constructed run. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationTransfer
open Shared.Beeping
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonControlRelocationInside
open Shared.PNP.Record285.PythonControlRelocationRun
open Shared.PNP.Record285.PythonControlSkip

def referenceEntry (s : Store) : Status := .live ⟨47,s,referenceBase⟩
def candidateEntry (s : Store) : Status := .live ⟨94,s,candidateBase⟩
def referenceExit (s : Store) : Status := .live ⟨65,s,referenceBase⟩
def candidateExit (s : Store) : Status := .live ⟨112,s,candidateBase⟩

theorem initial_matched (s : Store) : BoundedMatched (referenceEntry s) (candidateEntry s) := by
  simp [BoundedMatched,Matched,Inside,referenceEntry,candidateEntry]

theorem matched_exit (r : Status) (s : Store) (h : Matched r (candidateExit s)) :
    r = referenceExit s := by
  cases r with
  | fault => simp [candidateExit,Matched] at h
  | returned n => simp [candidateExit,Matched] at h
  | live r =>
    rcases h with ⟨hs,hpc,inner,hr,hc⟩
    change candidateBase = inner.map shiftLoop ++ candidateBase at hc
    have hh' : inner.map shiftLoop ++ candidateBase = [] ++ candidateBase := by
      simpa only [List.nil_append] using hc.symm
    have hh : inner.map shiftLoop = [] := List.append_cancel_right hh'
    have hnil : inner=[] := List.map_eq_nil_iff.mp hh
    cases r with
    | mk pc store loops =>
      simp only [candidateExit] at hs hpc hr
      simp [hnil] at hr
      have hpc' : pc=65 := by omega
      simp [referenceExit,hs,hpc',hr]

theorem run_advance (s : Status) (n : Nat) : (execution s).run n = pySystem.advance s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step code ((execution s).run n)).1 = (step code (pySystem.advance s n)).1
    rw [ih]

theorem transfer_segment (s out : Store) (n : Nat)
    (hsegment : Silent (candidateEntry s) (candidateExit out) n)
    (hbefore : ∀ t, t<n → BeforeBoundary ((execution (referenceEntry s)).run t)) :
    Silent (referenceEntry s) (referenceExit out) n := by
  obtain ⟨hm,hevents⟩ := bounded_runs _ _ (initial_matched s) n hbefore
  have hc : (execution (candidateEntry s)).run n = candidateExit out := by
    rw [run_advance]
    exact hsegment.1
  rw [hc] at hm
  constructor
  · rw [← run_advance]
    exact matched_exit _ out hm.1
  · intro t ht hbeep
    have he := hevents t ht
    have hnot := hsegment.2 t ht
    unfold EventSystem.BeepFrom at hbeep hnot
    rw [← run_advance] at hbeep hnot
    exact hnot (by simpa [pySystem] using he.symm.trans hbeep)

end Shared.PNP.Record285.PythonControlRelocationTransfer

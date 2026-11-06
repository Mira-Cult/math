import Shared.Beeping.NPcoNP.NativeHalfWindowDispatch

/-! Exact first-register test at the selector window, under the supplied
finite-layout hypotheses. This does not establish graph-state reachability. -/
namespace Shared.Beeping.NPcoNP.NativeHalfWindowBranch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfWindowDispatch
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- The third bit tests the first value of a window with another block. -/
theorem marker_window_first_value (x : Nat) (xs : List Nat) (hne : xs ≠ []) :
    ∃ rest, markerWindow (x::xs) = false :: true :: (if x=0 then false else true) :: rest := by
  obtain ⟨rest,hr⟩ := marker_window_prefix (x::xs) (by simp)
  have he := markerWindow_append_zero (x::xs)
  rw [hr] at he
  cases rest with
  | nil =>
    cases xs with
    | nil => contradiction
    | cons y ys =>
      cases x with
      | zero => simp [encode,block,List.replicate_succ] at he
      | succ x => simp [encode,block,List.replicate_succ] at he
  | cons b rest =>
    cases x with
    | zero =>
      have hb : b=false := by simpa [encode,block,List.replicate_succ] using congrArg (List.take 3) he
      subst b
      exact ⟨rest,by simpa using hr⟩
    | succ x =>
      have hb : b=true := by simpa [encode,block,List.replicate_succ] using congrArg (List.take 3) he
      subst b
      exact ⟨rest,by simpa using hr⟩

/-- After the state-93 and state-6 rows, the state-7 row tests whether the
first window value is zero, without writing the tape or emitting an event. -/
theorem selected_window_value_branch (back out : Int → Bool) (p : Int) (x : Nat)
    (xs : List Nat) (start : Config 284) (n : Nat)
    (hl : (x::xs).length=14)
    (hwin : Holds back (p-((encode (x::xs)).length : Int)) (markerWindow (x::xs)))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode (x::xs)).length : Int)) out) n) :
    silentSegment machine start
      (cfg (if x=0 then 6 else 8) (p-((encode (x::xs)).length : Int)+3) out) (n+3) := by
  have hne : xs ≠ [] := by intro h; simp [h] at hl
  obtain ⟨rest,he⟩ := marker_window_first_value x xs hne
  have hlen : 2<(encode (x::xs)).length := by
    have hm := markerWindow_length (x::xs)
    rw [he] at hm
    simp at hm
    omega
  have hbit : out (p-((encode (x::xs)).length : Int)+2) = (if x=0 then false else true) := by
    rw [hprefix _ (by omega)]
    rw [he] at hwin
    have hh := hwin.2.2.1
    convert hh using 1 <;> congr 1 <;> omega
  have hs := selected_window_to7 back out p (x::xs) start n hl hwin hprefix hseg
  by_cases hx : x=0
  · have hz : out (p-((encode (x::xs)).length : Int)+2)=false := by simpa [hx] using hbit
    have hnext := oneSeg machine _ _ (step7_zero _ out hz)
    have hr := segAdd machine _ _ _ (n+2) 1 hs hnext
    simp only [if_pos hx]
    convert hr using 1 <;> congr 1 <;> omega
  · have ho : out (p-((encode (x::xs)).length : Int)+2)=true := by simpa [hx] using hbit
    have hnext := oneSeg machine _ _ (step7_one _ out ho)
    have hr := segAdd machine _ _ _ (n+2) 1 hs hnext
    simp only [if_neg hx]
    convert hr using 1 <;> congr 1 <;> omega

#print axioms marker_window_first_value
#print axioms selected_window_value_branch
end Shared.Beeping.NPcoNP.NativeHalfWindowBranch

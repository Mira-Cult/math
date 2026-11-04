import Shared.PNP.Record285.PythonControlCandidate
import Shared.Beeping.BinaryReadWrite

/-! The actual typed candidate decoder's unary-skip loops. This establishes
finite segments in the partial control-flow model, not yet the complete
interpreter-to-controller refinement or CPython parser correctness. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlSkip
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlCandidate
open Shared.Beeping.BinaryReadWrite (advance_add)

def pySystem : EventSystem Status := ⟨.fault,step code⟩

def outer : List Loop := [⟨94,99⟩,⟨91,131⟩,⟨31,140⟩,⟨28,146⟩]
def inner : List Loop := ⟨96,98⟩::outer

def guard (s : Store) : Status := .live ⟨98,s,inner⟩
def entry (s : Store) : Status := .live ⟨96,s,outer⟩
def exit (s : Store) : Status := .live ⟨98,s,outer⟩

def Silent (a b : Status) (n : Nat) : Prop :=
  pySystem.advance a n = b ∧ ∀ t, t<n → ¬ pySystem.BeepFrom a t

theorem silent_trans {a b c : Status} {m n : Nat} (h₁ : Silent a b m) (h₂ : Silent b c n) :
    Silent a c (m+n) := by
  constructor
  · rw [advance_add,h₁.1]; exact h₂.1
  · intro t ht hb
    by_cases h : t < m
    · exact h₁.2 t h hb
    · apply h₂.2 (t-m) (by omega)
      unfold EventSystem.BeepFrom at hb ⊢
      have heq : t=m+(t-m) := by omega
      rw [heq,advance_add,h₁.1] at hb
      exact hb

theorem rows : code[96]? = lines19[1]? ∧ code[97]? = lines19[2]? ∧
    code[98]? = lines19[3]? ∧ seek code 97 20 = 98 := by decide

theorem guard_even (s : Store) (h : s "digit"%2 = 0) :
    Silent (guard s) (exit s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,guard,exit,inner,outer,settle,
      advance,rows,lines19,eval,op,h]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,inner,outer,
      settle,advance,rows,lines19,eval,op,h]

theorem guard_odd (s : Store) (h : s "digit"%2 = 1) :
    Silent (guard s) (guard (put s "digit" (s "digit"/2))) 2 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,guard,inner,outer,settle,
      advance,rows,lines19,eval,op,simple,augOp,put,h]
  · intro t ht
    have ht0 : t=0 ∨ t=1 := by omega
    rcases ht0 with rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,inner,outer,
        settle,advance,rows,lines19,eval,op,simple,augOp,put,h]

/-- The actual inner loop consumes the whole low-order unary one-run in
finite time, retaining the even delimiter and every unrelated store entry. -/
theorem unary_ones (digit : Nat) (s : Store) (hvalue : s "digit" = digit) :
    Silent (guard s) (exit (put s "digit" (2*(popUnary digit).2)))
      (2*(popUnary digit).1+1) := by
  induction digit using Nat.strongRecOn generalizing s with
  | ind digit ih =>
    by_cases ho : digit%2 = 1
    · have hp : 0 < digit := by omega
      let next := put s "digit" (digit/2)
      have hn : next "digit" = digit/2 := by simp [next,put]
      have hfirst : Silent (guard s) (guard next) 2 := by
        simpa [next,hvalue] using guard_odd s (by simpa [hvalue] using ho)
      have hrest := ih (digit/2) (by omega) next hn
      have hcombined := silent_trans hfirst hrest
      have heffect : put next "digit" (2*(popUnary (digit/2)).2) =
          put s "digit" (2*(popUnary (digit/2)).2) := by
        funext key
        simp [next,put]
        by_cases hk : key="digit" <;> simp [hk]
      have hpop : popUnary digit = ((popUnary (digit/2)).1+1,(popUnary (digit/2)).2) := by
        rw [popUnary]
        simp [ho]
      rw [hpop]
      simp only [Prod.fst,Prod.snd]
      rw [←heffect]
      convert hcombined using 1 <;> omega
    · have he : digit%2 = 0 := by omega
      have hdigit : 2*(digit/2) = digit := by omega
      have heffect : put s "digit" digit = s := by
        funext key
        by_cases hk : key="digit"
        · subst key; simp [put,hvalue]
        · simp [put,hk]
      have hpop : popUnary digit = (0,digit/2) := by rw [popUnary]; simp [ho]
      rw [hpop]
      simp only [Prod.fst,Prod.snd,Nat.mul_zero,Nat.zero_add,hdigit,heffect]
      exact guard_even s (by simpa [hvalue] using he)

/-- Equivalent first transitions imply equal nonempty futures, even if the
two configurations differ by a pending administrative dedent. -/
theorem same_future {a b : Status} (h : pySystem.step a = pySystem.step b) (n : Nat) :
    pySystem.advance a (n+1) = pySystem.advance b (n+1) := by
  induction n with
  | zero => simpa [EventSystem.advance] using congrArg Prod.fst h
  | succ n ih => simpa [EventSystem.advance] using congrArg (fun x => (pySystem.step x).1) ih

theorem same_silent {a b c : Status} {n : Nat}
    (hstep : pySystem.step a = pySystem.step b) (hpos : 0 < n) (h : Silent b c n) :
    Silent a c n := by
  constructor
  · cases n with
    | zero => omega
    | succ n => rw [same_future hstep n]; exact h.1
  · intro t ht he
    apply h.2 t ht
    cases t with
    | zero => simpa [EventSystem.BeepFrom,EventSystem.advance,hstep] using he
    | succ t => simpa [EventSystem.BeepFrom,same_future hstep t] using he

theorem entry_step (s : Store) : pySystem.step (entry s) = pySystem.step (guard s) := by rfl

theorem unary_from_entry (s : Store) :
    Silent (entry s) (exit (put s "digit" (2*(popUnary (s "digit")).2)))
      (2*(popUnary (s "digit")).1+1) := by
  apply same_silent (entry_step s) (by omega)
  exact unary_ones (s "digit") s rfl

def context : List Loop := [⟨91,131⟩,⟨31,140⟩,⟨28,146⟩]
def outerGuard (s : Store) : Status := .live ⟨99,s,outer⟩
def outerExit (s : Store) : Status := .live ⟨99,s,context⟩

theorem outer_rows : code[94]? = lines18[4]? ∧ code[95]? = lines19[0]? ∧
    seek code 95 16 = 99 := by decide

theorem outer_zero (s : Store) (h : s "state" = 0) :
    Silent (outerGuard s) (outerExit s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,outerGuard,outerExit,outer,context,
      settle,advance,outer_rows,lines18,eval,h]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,outerGuard,outer,context,
      settle,advance,outer_rows,lines18,eval,h]

/-- One positive outer iteration decrements the selector, skips exactly one
unary record, preserves the complete remaining store, and emits no event. -/
theorem outer_cycle (s : Store) (h : 0 < s "state") :
    ∃ n, 0 < n ∧ Silent (outerGuard s)
      (outerGuard (put (put s "state" (s "state"-1)) "digit" (popUnary (s "digit")).2)) n := by
  let marked := put s "state" (s "state"-1)
  have hprefix : Silent (outerGuard s) (entry marked) 2 := by
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,outerGuard,entry,outer,context,
        settle,advance,outer_rows,lines18,lines19,eval,simple,op,augOp,put,marked,
        show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega]
    · intro t ht
      have hc : t=0 ∨ t=1 := by omega
      rcases hc with rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,outerGuard,entry,
          outer,context,settle,advance,outer_rows,lines18,lines19,eval,simple,op,augOp,
          put,marked,show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega]
  have hinner := unary_from_entry marked
  let after := put marked "digit" (2*(popUnary (marked "digit")).2)
  have hdigit : after "digit" = 2*(popUnary (s "digit")).2 := by simp [after,marked,put]
  have hlast : Silent (exit after)
      (outerGuard (put marked "digit" (popUnary (s "digit")).2)) 1 := by
    have heffect : put after "digit" (after "digit"/2) =
        put marked "digit" (popUnary (s "digit")).2 := by
      funext key
      by_cases hk : key="digit" <;> simp [after,marked,put,hk,hdigit]
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,exit,outerGuard,outer,settle,advance,
        rows,lines19,eval,simple,op,augOp,heffect]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,exit,outer,settle,
        advance,rows,lines19,eval,simple,op,augOp]
  have hcombined := silent_trans (silent_trans hprefix hinner) hlast
  refine ⟨2+(2*(popUnary (s "digit")).1+1)+1,by omega,?_⟩
  simpa [after,marked,put] using hcombined

/-- The complete candidate unary-record skip terminates for every finite
selector and digit, preserving the entire remaining store and producing no
marked event. -/
theorem outer_all (count : Nat) (s : Store) (hcount : s "state" = count) :
    ∃ n, 0 < n ∧ Silent (outerGuard s)
      (outerExit (put (put s "state" 0) "digit" (skipUnary count (s "digit")))) n := by
  induction count generalizing s with
  | zero =>
    have hz : s "state" = 0 := hcount
    have heffect : put (put s "state" 0) "digit" (skipUnary 0 (s "digit")) = s := by
      funext key
      by_cases hstate : key="state" <;> by_cases hdigit : key="digit" <;>
        simp [put,skipUnary,hstate,hdigit,hz]
    rw [heffect]
    exact ⟨1,by decide,outer_zero s hz⟩
  | succ count ih =>
    have hp : 0 < s "state" := by omega
    let next := put (put s "state" (s "state"-1)) "digit" (popUnary (s "digit")).2
    have hn : next "state" = count := by simp [next,put,hcount]
    obtain ⟨d,hd,hcycle⟩ := outer_cycle s hp
    obtain ⟨e,he,hrest⟩ := ih next hn
    have heffect : put (put next "state" 0) "digit" (skipUnary count (next "digit")) =
        put (put s "state" 0) "digit" (skipUnary (count+1) (s "digit")) := by
      funext key
      by_cases hstate : key="state" <;> by_cases hdigit : key="digit" <;>
        simp [next,put,skipUnary,hstate,hdigit]
    have h := silent_trans hcycle hrest
    refine ⟨d+e,by omega,?_⟩
    simpa [next,heffect] using h

/-- The actual first visit to row 94 has the same transition as the pending
dedent form used in the loop induction. -/
theorem outer_entry_step (s : Store) :
    pySystem.step (.live ⟨94,s,context⟩) = pySystem.step (outerGuard s) := by rfl

theorem candidate_skip_terminates (s : Store) :
    ∃ n, 0 < n ∧ Silent (.live ⟨94,s,context⟩)
      (outerExit (put (put s "state" 0) "digit" (skipUnary (s "state") (s "digit")))) n := by
  obtain ⟨n,hn,hquiet⟩ := outer_all (s "state") s rfl
  exact ⟨n,hn,same_silent (outer_entry_step s) hn hquiet⟩

end Shared.PNP.Record285.PythonControlSkip

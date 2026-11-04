import Shared.PNP.Record285.PythonControlRelocationCandidate

/-! Composable silent segments which stay before the candidate decoder exit.
This is the explicit hypothesis of the reference/candidate segment transfer. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlGuarded
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlRelocationCandidate
open Shared.Beeping.BinaryReadWrite (advance_add)

def Guarded (a b : Status) (n : Nat) : Prop :=
  Silent a b n ∧ ∀ t, t<n → CandidateBefore (pySystem.advance a t)

theorem guarded_trans {a b c : Status} {m n : Nat}
    (h₁ : Guarded a b m) (h₂ : Guarded b c n) : Guarded a c (m+n) := by
  refine ⟨silent_trans h₁.1 h₂.1,?_⟩
  intro t ht
  by_cases h : t<m
  · exact h₁.2 t h
  · have heq : t=m+(t-m) := by omega
    rw [heq,advance_add,h₁.1.1]
    exact h₂.2 (t-m) (by omega)

theorem guarded_same {a b c : Status} {n : Nat}
    (hstep : pySystem.step a=pySystem.step b) (hpos : 0<n)
    (ha : CandidateBefore a) (h : Guarded b c n) : Guarded a c n := by
  refine ⟨same_silent hstep hpos h.1,?_⟩
  intro t ht
  cases t with
  | zero => simpa [EventSystem.advance] using ha
  | succ t =>
    rw [same_future hstep t]
    exact h.2 (t+1) ht

theorem guard_even (s : Store) (h : s "digit"%2=0) :
    Guarded (guard s) (exit s) 1 := by
  refine ⟨PythonControlSkip.guard_even s h,?_⟩
  intro t ht
  have : t=0 := by omega
  subst t
  simp [pySystem,EventSystem.advance,CandidateBefore,PythonControlSkip.guard,inner,outer,settle]

theorem guard_odd (s : Store) (h : s "digit"%2=1) :
    Guarded (guard s) (guard (put s "digit" (s "digit"/2))) 2 := by
  refine ⟨PythonControlSkip.guard_odd s h,?_⟩
  intro t ht
  have ht0 : t=0 ∨ t=1 := by omega
  have hr : code[96]? = some (.while_ 20 (.binary .mod (.name "digit") (.num 2))) := by
    simpa [lines19] using PythonControlSkip.rows.1
  have hseek : seek code 97 20 = 98 := PythonControlSkip.rows.2.2.2
  rcases ht0 with rfl|rfl <;>
    simp [pySystem,EventSystem.advance,CandidateBefore,step,PythonControlSkip.guard,inner,outer,settle,
      advance,hr,eval,op,h,hseek]

theorem unary_ones (digit : Nat) (s : Store) (hvalue : s "digit" = digit) :
    Guarded (guard s) (exit (put s "digit" (2*(popUnary digit).2)))
      (2*(popUnary digit).1+1) := by
  induction digit using Nat.strongRecOn generalizing s with
  | ind digit ih =>
    by_cases ho : digit%2 = 1
    · have hp : 0 < digit := by omega
      let next := put s "digit" (digit/2)
      have hn : next "digit" = digit/2 := by simp [next,put]
      have hfirst : Guarded (guard s) (guard next) 2 := by
        simpa [next,hvalue] using guard_odd s (by simpa [hvalue] using ho)
      have hrest := ih (digit/2) (by omega) next hn
      have hcombined := guarded_trans hfirst hrest
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



theorem unary_from_entry (s : Store) :
    Guarded (entry s) (exit (put s "digit" (2*(popUnary (s "digit")).2)))
      (2*(popUnary (s "digit")).1+1) := by
  apply guarded_same (entry_step s) (by omega)
  · simp [CandidateBefore,entry,outer,settle]
  · exact unary_ones (s "digit") s rfl

theorem outer_zero (s : Store) (h : s "state" = 0) :
    Guarded (outerGuard s) (outerExit s) 1 := by
  refine ⟨PythonControlSkip.outer_zero s h,?_⟩
  intro t ht
  have : t=0 := by omega
  subst t
  simp [EventSystem.advance,CandidateBefore,outerGuard,outer,context,settle]

theorem outer_prefix (s : Store) (h : 0 < s "state") :
    Guarded (outerGuard s) (entry (put s "state" (s "state"-1))) 2 := by
  constructor
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,outerGuard,entry,outer,context,
        settle,advance,outer_rows,lines18,lines19,eval,simple,op,augOp,put,
        show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega]
    · intro t ht
      have hc : t=0 ∨ t=1 := by omega
      rcases hc with rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,outerGuard,entry,
          outer,context,settle,advance,outer_rows,lines18,lines19,eval,simple,op,augOp,
          put,show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega]
  · intro t ht
    have hc : t=0 ∨ t=1 := by omega
    rcases hc with rfl|rfl <;>
      simp [pySystem,EventSystem.advance,CandidateBefore,step,outerGuard,outer,context,
        settle,advance,outer_rows,lines18,eval,op,show s "state" ≠ 0 by omega]


theorem outer_cycle (s : Store) (h : 0 < s "state") :
    ∃ n, 0 < n ∧ Guarded (outerGuard s)
      (outerGuard (put (put s "state" (s "state"-1)) "digit" (popUnary (s "digit")).2)) n := by
  let marked := put s "state" (s "state"-1)
  have hprefix : Guarded (outerGuard s) (entry marked) 2 := outer_prefix s h
  have hinner := unary_from_entry marked
  let after := put marked "digit" (2*(popUnary (marked "digit")).2)
  have hdigit : after "digit" = 2*(popUnary (s "digit")).2 := by simp [after,marked,put]
  have hlast : Guarded (exit after)
      (outerGuard (put marked "digit" (popUnary (s "digit")).2)) 1 := by
    have heffect : put after "digit" (after "digit"/2) =
        put marked "digit" (popUnary (s "digit")).2 := by
      funext key
      by_cases hk : key="digit" <;> simp [after,marked,put,hk,hdigit]
    constructor
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,exit,outerGuard,outer,settle,advance,
          PythonControlSkip.rows,lines19,eval,simple,op,augOp,heffect]
      · intro t ht
        have ht0 : t=0 := by omega
        subst t
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,exit,outer,settle,
          advance,PythonControlSkip.rows,lines19,eval,simple,op,augOp]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [EventSystem.advance,CandidateBefore,exit,outer,settle]
  have hcombined := guarded_trans (guarded_trans hprefix hinner) hlast
  refine ⟨2+(2*(popUnary (s "digit")).1+1)+1,by omega,?_⟩
  simpa [after,marked,put] using hcombined

theorem outer_all (count : Nat) (s : Store) (hcount : s "state" = count) :
    ∃ n, 0 < n ∧ Guarded (outerGuard s)
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
    have h := guarded_trans hcycle hrest
    refine ⟨d+e,by omega,?_⟩
    simpa [next,heffect] using h


theorem candidate_skip_terminates (s : Store) :
    ∃ n, 0 < n ∧ Guarded (.live ⟨94,s,context⟩)
      (outerExit (put (put s "state" 0) "digit" (skipUnary (s "state") (s "digit")))) n := by
  obtain ⟨n,hn,hquiet⟩ := outer_all (s "state") s rfl
  refine ⟨n,hn,guarded_same (outer_entry_step s) hn ?_ hquiet⟩
  simp [CandidateBefore,context,settle]

end Shared.PNP.Record285.PythonControlGuarded

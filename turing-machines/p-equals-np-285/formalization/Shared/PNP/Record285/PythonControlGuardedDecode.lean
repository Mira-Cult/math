import Shared.PNP.Record285.PythonControlGuarded

/-! Boundary-aware finite carry decoding in the candidate interpreter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlGuardedDecode
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent context silent_trans outerExit)
open Shared.PNP.Record285.PythonControlDecode
open Shared.PNP.Record285.PythonControlRelocationCandidate
open Shared.PNP.Record285.PythonControlGuarded

theorem guard_even (s : Store) (h : s "digit"%2=0) :
    Guarded (PythonControlDecode.guard s) (PythonControlDecode.exit s) 1 := by
  refine ⟨PythonControlDecode.guard_even s h,?_⟩
  intro t ht
  have : t=0 := by omega
  subst t
  simp [EventSystem.advance,CandidateBefore,PythonControlDecode.guard,decodeLoop,context,settle,flow]

theorem guard_odd (s : Store) (h : s "digit"%2=1) :
    ∃ n, 0 < n ∧ Guarded (PythonControlDecode.guard s) (PythonControlDecode.guard (cycleStore s)) n := by
  by_cases hw : s "write"=0
  · refine ⟨4,by decide,⟨?_,?_⟩⟩
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,settle,
          advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,cycleStore]
      · intro t ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
        rcases hc with rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,
            settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw]
    · intro t ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
      rcases hc with rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.advance,CandidateBefore,step,PythonControlDecode.guard,decodeLoop,context,
          settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw]
  · by_cases hd : s "direction"=0
    · refine ⟨7,by decide,⟨?_,?_⟩⟩
      · constructor
        · simp [Silent,pySystem,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,settle,
            advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd,cycleStore]
        · intro t ht
          have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
          rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,
              settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]
      · intro t ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.advance,CandidateBefore,step,PythonControlDecode.guard,decodeLoop,context,
            settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]
    · refine ⟨9,by decide,⟨?_,?_⟩⟩
      · constructor
        · simp [Silent,pySystem,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,settle,
            advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd,cycleStore]
        · intro t ht
          have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 := by omega
          rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
            simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,PythonControlDecode.guard,decodeLoop,context,
              settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]
      · intro t ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.advance,CandidateBefore,step,PythonControlDecode.guard,decodeLoop,context,
            settle,advance,PythonControlDecode.rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]

theorem decode_loop (digit : Nat) (s : Store) (d : PythonInlineDecoder.Digits) :
    ∃ n, 0 < n ∧ Guarded (PythonControlDecode.guard (storeOf s digit d))
      (PythonControlDecode.exit (storeOf s (2*(popUnary digit).2)
        (PythonInlineDecoder.bumpN (popUnary digit).1 d))) n := by
  induction digit using Nat.strongRecOn generalizing s d with
  | ind digit ih =>
    by_cases ho : digit%2=1
    · have hp : 0 < digit := by omega
      obtain ⟨n,hn,hfirst⟩ := guard_odd (storeOf s digit d) (by simpa using ho)
      rw [cycle_storeOf] at hfirst
      obtain ⟨m,hm,hrest⟩ := ih (digit/2) (by omega) s (PythonInlineDecoder.bump d)
      have h := guarded_trans hfirst hrest
      have hpop : popUnary digit = ((popUnary (digit/2)).1+1,(popUnary (digit/2)).2) := by
        rw [popUnary]; simp [ho]
      refine ⟨n+m,by omega,?_⟩
      rw [hpop]
      simpa [PythonInlineDecoder.bumpN] using h
    · have he : digit%2=0 := by omega
      have hdigit : 2*(digit/2) = digit := by omega
      have hpop : popUnary digit = (0,digit/2) := by rw [popUnary]; simp [ho]
      refine ⟨1,by decide,?_⟩
      rw [hpop]
      simpa [PythonInlineDecoder.bumpN,hdigit] using
        guard_even (storeOf s digit d) (by simpa using he)


theorem decode_from_entry (digit : Nat) (s : Store) (d : PythonInlineDecoder.Digits) :
    ∃ n, 0 < n ∧ Guarded (PythonControlDecode.entry (storeOf s digit d))
      (PythonControlDecode.exit (storeOf s (2*(popUnary digit).2)
        (PythonInlineDecoder.bumpN (popUnary digit).1 d))) n := by
  obtain ⟨n,hn,h⟩ := decode_loop digit s d
  refine ⟨n,hn,guarded_same (PythonControlDecode.entry_step _) hn ?_ h⟩
  simp [CandidateBefore,PythonControlDecode.entry,context,settle]

theorem candidate_decode_terminates (s : Store) :
    ∃ n, 0 < n ∧ Guarded (outerExit s)
      (.live ⟨112,storeOf s (popUnary (s "digit")).2
        (PythonInlineDecoder.bumpN (popUnary (s "digit")).1 ⟨false,false,0⟩),context⟩) n := by
  let zero : PythonInlineDecoder.Digits := ⟨false,false,0⟩
  have hinitSilent : Silent (outerExit s) (PythonControlDecode.entry (storeOf s (s "digit") zero)) 1 := by
    have heffect : put (put (put s "write" 0) "direction" 0) "state" 0 =
        storeOf s (s "digit") zero := by
      funext key
      by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
        by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
        simp [storeOf,zero,put,hd,hw,hr,hs]
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,outerExit,PythonControlDecode.entry,context,settle,advance,
        PythonControlDecode.rows,lines19,simple,values,eval,assignAll,heffect]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,outerExit,context,
        settle,advance,PythonControlDecode.rows,lines19,simple,values,eval,assignAll]
  have hinit : Guarded (outerExit s) (PythonControlDecode.entry (storeOf s (s "digit") zero)) 1 := by
    refine ⟨hinitSilent,?_⟩
    intro t ht
    have : t=0 := by omega
    subst t
    simp [EventSystem.advance,CandidateBefore,outerExit,context,settle]
  obtain ⟨m,hm,hloop⟩ := decode_from_entry (s "digit") s zero
  let d := PythonInlineDecoder.bumpN (popUnary (s "digit")).1 zero
  let after := storeOf s (2*(popUnary (s "digit")).2) d
  have hlastSilent : Silent (PythonControlDecode.exit after) (.live ⟨112,storeOf s (popUnary (s "digit")).2 d,context⟩) 1 := by
    have heffect : put after "digit" (after "digit"/2) = storeOf s (popUnary (s "digit")).2 d := by
      funext key
      by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
        by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
        simp [after,storeOf,put,hd,hw,hr,hs]
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,PythonControlDecode.exit,context,settle,advance,
        PythonControlDecode.rows,lines22,simple,eval,op,augOp,heffect]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,PythonControlDecode.exit,context,
        settle,advance,PythonControlDecode.rows,lines22,simple,eval,op,augOp]
  have hlast : Guarded (PythonControlDecode.exit after) (.live ⟨112,storeOf s (popUnary (s "digit")).2 d,context⟩) 1 := by
    refine ⟨hlastSilent,?_⟩
    intro t ht
    have : t=0 := by omega
    subst t
    simp [EventSystem.advance,CandidateBefore,PythonControlDecode.exit,context,settle]
  have h := guarded_trans (guarded_trans hinit hloop) hlast
  refine ⟨1+m+1,by omega,?_⟩
  simpa [after,d,zero] using h


theorem candidate_record_terminates (s : Store) :
    let stream := skipUnary (s "state") (s "digit")
    ∃ n, 0 < n ∧ Guarded (.live ⟨94,s,context⟩)
      (.live ⟨112,storeOf s (popUnary stream).2
        (PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩),context⟩) n := by
  let stream := skipUnary (s "state") (s "digit")
  let mid := put (put s "state" 0) "digit" stream
  have hmid : mid "digit" = stream := by simp [mid,put]
  obtain ⟨n,hn,hskip⟩ := PythonControlGuarded.candidate_skip_terminates s
  obtain ⟨m,hm,hdecode⟩ := candidate_decode_terminates mid
  rw [hmid] at hdecode
  have heffect (tail : Nat) (d : PythonInlineDecoder.Digits) :
      storeOf mid tail d = storeOf s tail d := by
    funext key
    by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
      by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
      simp [mid,storeOf,put,hd,hw,hr,hs]
  rw [heffect] at hdecode
  refine ⟨n+m,by omega,?_⟩
  exact guarded_trans hskip hdecode


end Shared.PNP.Record285.PythonControlGuardedDecode

import Shared.PNP.Record285.PythonControlReferenceTick

/-! The complete bounded reference branch, for arbitrary finite stores and
clocks. The enclosing branch enumeration remains a separate obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceEvaluator
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControlSkip (Silent silent_trans)
open Shared.PNP.Record285.PythonControlReferenceClock
open Shared.PNP.Record285.PythonControlReferenceClockMeaning
open Shared.PNP.Record285.PythonControlReferenceTick

theorem reference_loop (clock : Nat) (s : Store) (hclock : s "steps"=clock) :
    ∃ n out, 0<n ∧ Silent (pending s) (done out) n ∧
      out "program"=s "program" ∧ out "radix"=s "radix" ∧ out "remaining"=s "remaining" ∧
      out "n"=s "n" ∧ out "exponent"=s "exponent" ∧
      out "expected" = (if haltedWithin (s "radix"+s "remaining") clock (sourceState s)
        then 1 else s "expected") ∧
      out "branches" = (if haltedWithin (s "radix"+s "remaining") clock (sourceState s)
        then 0 else s "branches") := by
  induction clock generalizing s with
  | zero =>
    refine ⟨1,s,by decide,zero_tick s hclock,rfl,rfl,rfl,rfl,rfl,?_,?_⟩ <;> simp [haltedWithin]
  | succ clock ih =>
    have hp : 0 < s "steps" := by omega
    obtain ⟨n,mid,loops,hn,hsegment,hsteps,hprogram,hradix,hremaining,hname,hexponent,hresult⟩ :=
      positive_tick_matches s hp
    cases hsim : simStep (s "radix"+s "remaining") (sourceState s) with
    | none =>
      simp only [hsim] at hresult
      obtain ⟨hloops,hexpected,hbranches⟩ := hresult
      subst loops
      refine ⟨n,mid,hn,hsegment,hprogram,hradix,hremaining,hname,hexponent,?_,?_⟩
      · simpa [haltedWithin,hsim] using hexpected
      · simpa [haltedWithin,hsim] using hbranches
    | some next =>
      simp only [hsim] at hresult
      obtain ⟨hloops,hnext,hexpected,hbranches⟩ := hresult
      subst loops
      have hmid : mid "steps"=clock := by omega
      obtain ⟨m,out,hm,hrest,hpout,hrout,hremout,hnout,hexpout,heout,hbout⟩ := ih mid hmid
      refine ⟨n+m,out,by omega,silent_trans hsegment hrest,
        hpout.trans hprogram,hrout.trans hradix,hremout.trans hremaining,
        hnout.trans hname,hexpout.trans hexponent,?_,?_⟩
      · simpa [haltedWithin,hsim,hradix,hremaining,hnext,hexpected] using heout
      · simpa [haltedWithin,hsim,hradix,hremaining,hnext,hbranches] using hbout

end Shared.PNP.Record285.PythonControlReferenceEvaluator

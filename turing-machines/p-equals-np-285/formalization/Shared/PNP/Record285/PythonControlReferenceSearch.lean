import Shared.PNP.Record285.PythonControlReferenceBranch

/-! Descending, finite reference-branch enumeration in the typed interpreter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceSearch
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControlSkip (Silent silent_trans same_silent)
open Shared.PNP.Record285.PythonControlReferenceClockMeaning (sourceState)
open Shared.PNP.Record285.PythonControlReferenceEvaluator
open Shared.PNP.Record285.PythonControlReferenceBranch

theorem prepared_fields (s : Store) :
    (prepared s) "branches" = s "branches"-1 ∧ (prepared s) "steps" = s "n" ∧
    (prepared s) "program"=s "program" ∧ (prepared s) "radix"=s "radix" ∧
    (prepared s) "remaining"=s "remaining" ∧ (prepared s) "n"=s "n" ∧
    (prepared s) "exponent"=s "exponent" ∧ (prepared s) "expected"=s "expected" ∧
    sourceState (prepared s)=⟨0,0,0,s "branches"-1⟩ := by
  simp [prepared,put,sourceState]

theorem search_loop (count : Nat) (s : Store) (hcount : s "branches"=count)
    (hexpected : s "expected"=0) :
    ∃ n out, 0<n ∧ Silent (pending s) (done out) n ∧
      out "program"=s "program" ∧ out "radix"=s "radix" ∧ out "remaining"=s "remaining" ∧
      out "n"=s "n" ∧ out "exponent"=s "exponent" ∧ out "branches"=0 ∧
      out "expected" = (if referenceSearch (s "radix"+s "remaining") (s "n") count then 1 else 0) := by
  induction count generalizing s with
  | zero =>
    refine ⟨1,s,by decide,zero_branch s hcount,rfl,rfl,rfl,rfl,rfl,hcount,?_⟩
    simpa [referenceSearch] using hexpected
  | succ count ih =>
    have hp : 0<s "branches" := by omega
    let p := prepared s
    have hf := prepared_fields s
    have hpbranch : p "branches" = s "branches"-1 := hf.1
    have hpradix : p "radix" = s "radix" := hf.2.2.2.1
    have hpremaining : p "remaining" = s "remaining" := hf.2.2.2.2.1
    have hpname : p "n" = s "n" := hf.2.2.2.2.2.1
    have hpexpected : p "expected" = s "expected" := hf.2.2.2.2.2.2.2.1
    have hstart := positive_branch s hp
    have hsteps : p "steps"=s "n" := hf.2.1
    obtain ⟨m,mid,hm,hbranch,hprogram,hradix,hremaining,hname,hexponent,hvalue,hcounter⟩ :=
      reference_loop (s "n") p hsteps
    have hbranch' := same_silent (PythonControlReferenceClock.head_step p) hm hbranch
    have hbefore := silent_trans hstart hbranch'
    have hsource : sourceState p = ⟨0,0,0,count⟩ := by
      have heq := hf.2.2.2.2.2.2.2.2
      simpa [hcount] using heq
    have heval : haltedWithin (p "radix"+p "remaining") (s "n") (sourceState p) =
        haltedWithin (s "radix"+s "remaining") (s "n") ⟨0,0,0,count⟩ := by
      rw [hpradix,hpremaining,hsource]
    let result := haltedWithin (s "radix"+s "remaining") (s "n") ⟨0,0,0,count⟩
    by_cases hresult : result = true
    · have hzero : mid "branches"=0 := by simpa [heval,result,hresult] using hcounter
      have hone : mid "expected"=1 := by simpa [heval,result,hresult] using hvalue
      have hfinish := zero_branch mid hzero
      refine ⟨7+m+1,mid,by omega,silent_trans hbefore hfinish,
        hprogram.trans hf.2.2.1,hradix.trans hf.2.2.2.1,
        hremaining.trans hf.2.2.2.2.1,hname.trans hf.2.2.2.2.2.1,
        hexponent.trans hf.2.2.2.2.2.2.1,hzero,?_⟩
      simpa [referenceSearch,result,hresult] using hone
    · have hfalse : result=false := Bool.eq_false_iff.mpr hresult
      have hmidcount : mid "branches"=count := by
        simpa [heval,result,hfalse,hpbranch,hcount] using hcounter
      have hmidexpected : mid "expected"=0 := by
        simpa [heval,result,hfalse,hpexpected,hexpected] using hvalue
      obtain ⟨k,out,hk,hrest,hpout,hrout,hremout,hnout,heout,houtzero,houtvalue⟩ :=
        ih mid hmidcount hmidexpected
      refine ⟨7+m+k,out,by omega,silent_trans hbefore hrest,
        hpout.trans (hprogram.trans hf.2.2.1),hrout.trans (hradix.trans hf.2.2.2.1),
        hremout.trans (hremaining.trans hf.2.2.2.2.1),hnout.trans (hname.trans hf.2.2.2.2.2.1),
        heout.trans (hexponent.trans hf.2.2.2.2.2.2.1),houtzero,?_⟩
      simpa [referenceSearch,result,hfalse,hradix,hremaining,hname,
        hpradix,hpremaining,hpname] using houtvalue

end Shared.PNP.Record285.PythonControlReferenceSearch

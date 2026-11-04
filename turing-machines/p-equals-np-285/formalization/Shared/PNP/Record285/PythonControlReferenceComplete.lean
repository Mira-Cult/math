import Shared.PNP.Record285.PythonControlReferenceSearch

/-! End-to-end finite reference computation in the typed interpreter, from
initializing the branch search through dispatch to candidate setup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceComplete
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent silent_trans same_silent)
open Shared.PNP.Record285.PythonControlReferenceBranch
open Shared.PNP.Record285.PythonControlReferenceSearch

def initial (s : Store) : Status := .live ⟨32,s,outer⟩
def initialized (s : Store) : Store := put (put s "expected" 0) "branches" (s "radix")

theorem rows : code[32]?=lines6[2]? ∧ code[33]?=lines6[3]? := by decide

theorem initial_segment (s : Store) : Silent (initial s) (head (initialized s)) 2 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,initial,head,outer,settle,advance,
      rows,lines6,simple,eval,put,initialized]
  · intro t ht
    have ht0 : t=0 ∨ t=1 := by omega
    rcases ht0 with rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,initial,outer,settle,advance,
        rows,lines6,simple,eval,put]

theorem reference_complete (s : Store) :
    ∃ n out, 0<n ∧ Silent (initial s) (done out) n ∧
      out "program"=s "program" ∧ out "radix"=s "radix" ∧ out "remaining"=s "remaining" ∧
      out "n"=s "n" ∧ out "exponent"=s "exponent" ∧ out "branches"=0 ∧
      out "expected" = (if reference (s "n") (s "radix") (s "remaining") then 1 else 0) := by
  let p := initialized s
  have hbranches : p "branches"=s "radix" := by simp [p,initialized,put]
  have hexpected : p "expected"=0 := by simp [p,initialized,put]
  obtain ⟨n,out,hn,hsearch,hprogram,hradix,hremaining,hname,hexponent,hzero,hresult⟩ :=
    search_loop (s "radix") p hbranches hexpected
  have hsearch' := same_silent (head_step p) hn hsearch
  refine ⟨2+n,out,by omega,silent_trans (initial_segment s) hsearch',?_,?_,?_,?_,?_,hzero,?_⟩
  · simpa [p,initialized,put] using hprogram
  · simpa [p,initialized,put] using hradix
  · simpa [p,initialized,put] using hremaining
  · simpa [p,initialized,put] using hname
  · simpa [p,initialized,put] using hexponent
  · have hpr : p "radix" = s "radix" := by simp [p,initialized,put]
    have hpm : p "remaining" = s "remaining" := by simp [p,initialized,put]
    have hpn : p "n" = s "n" := by simp [p,initialized,put]
    rw [hpr,hpm,hpn] at hresult
    change out "expected" = (if referenceSearch (s "radix"+s "remaining")
      (s "n") (s "radix") then 1 else 0)
    exact hresult

end Shared.PNP.Record285.PythonControlReferenceComplete

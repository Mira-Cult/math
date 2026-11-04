import Shared.PNP.Record285.PythonControlReferenceComplete
import Shared.PNP.Record285.PythonControlCandidateFrame

/-! Compose the complete typed reference and candidate phases. The
comparison value is the source mismatch bit, with its live input frame paid. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlComparison
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (Silent silent_trans)
open Shared.PNP.Record285.PythonControlCandidateFrame
open Shared.PNP.Record285.PythonControlReferenceComplete

theorem comparison_complete (s : Store) (hradix : 0 < s "radix") :
    ∃ n out, 0<n ∧ Silent (initial s) (PythonControlClock.done out) n ∧
      out "program"=s "program" ∧ out "exponent"=s "exponent" ∧
      out "n"=s "n" ∧ out "radix"=s "radix" ∧ out "remaining"=s "remaining" ∧
      out "expected" = (if mismatch (s "program") (s "exponent")
        (s "n") (s "radix") (s "remaining") then 1 else 0) := by
  obtain ⟨n,mid,hn,href,hprogram,hradix',hremaining,hname,hexponent,hzero,hreference⟩ :=
    reference_complete s
  have hstart : Silent (initial s)
      (.live ⟨82,mid,PythonControlCandidate.frames⟩) n := by
    simpa [PythonControlReferenceBranch.done,PythonControlReferenceBranch.outer,
      PythonControlCandidate.frames] using href
  have hmidradix : 0 < mid "radix" := by omega
  obtain ⟨m,out,hm,hcand,houtprog,hframe,hvalue⟩ := candidate_from_setup_frame mid hmidradix
  have hname' : out "n"=mid "n" := hframe "n" (by simp [Protected])
  have hexponent' : out "exponent"=mid "exponent" := hframe "exponent" (by simp [Protected])
  have hradix'' : out "radix"=mid "radix" := hframe "radix" (by simp [Protected])
  have hremaining' : out "remaining"=mid "remaining" := hframe "remaining" (by simp [Protected])
  refine ⟨n+m,out,by omega,silent_trans hstart hcand,houtprog.trans hprogram,
    hexponent'.trans hexponent,hname'.trans hname,hradix''.trans hradix',
    hremaining'.trans hremaining,?_⟩
  rw [hprogram,hexponent,hname,hradix',hremaining,hreference] at hvalue
  cases hr : reference (s "n") (s "radix") (s "remaining") <;>
    cases hc : candidate (s "program") (s "exponent") (s "n") (s "radix") (s "remaining") <;>
    simpa [mismatch,hr,hc] using hvalue

end Shared.PNP.Record285.PythonControlComparison

import Shared.PNP.Record285.PythonStraight
import Shared.PNP.Record285.PythonInlineController

/-! The typed source's complete deterministic-candidate setup block, checked
against the natural source model on positive radix. This is not yet a proof
of full Python control-flow semantics. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonCandidateSetup
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight

def output (s : Store) : Store :=
  let f := frame (s "radix") (s "remaining")
  put (put (put (put s "steps" ((s "n"+2)^(s "exponent"))) "left" 0)
    "state" (2*(f%2))) "right" (f/2)

/-- The actual checked lines construct the source's clock, scanned-bit
selector, and right-tape value; all other store entries are preserved. -/
theorem candidate_setup_exact (s : Store) (hradix : 0 < s "radix") :
    candidateSetup s = some (output s) := by
  have hpositive : 1 ≤ 2*(s "remaining"*s "radix") + s "radix" := by omega
  have hmod : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 0
  · simp [candidateSetup,output,frame,Shared.PNP.Record285.PythonSyntax.lines16,
      Shared.PNP.Record285.PythonSyntax.lines17,Shared.PNP.Record285.PythonSyntax.lines18,
      sequence,simple,eval,op,augOp,ifOne,put,hpositive,hz]
    funext key
    simp [put]
    by_cases hk : key = "right" <;> by_cases hs : key = "state" <;> simp [hk,hs]
  · have hone : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 1 := by omega
    simp [candidateSetup,output,frame,Shared.PNP.Record285.PythonSyntax.lines16,
      Shared.PNP.Record285.PythonSyntax.lines17,Shared.PNP.Record285.PythonSyntax.lines18,
      sequence,simple,eval,op,augOp,ifOne,put,hpositive,hone]
    funext key
    simp [put]
    by_cases hk : key = "right" <;> by_cases hs : key = "state" <;> simp [hk,hs]

/-- The resulting initialized virtual configuration and exact clock are
the inputs used by the verified inline bounded evaluator. -/
theorem candidate_setup_handoff (s : Store) (hradix : 0 < s "radix") :
    ∃ out, candidateSetup s = some out ∧
      out "steps" = (s "n"+2)^(s "exponent") ∧
      (⟨out "left",out "right",out "state",0⟩ : SimState) =
        ⟨0,(frame (s "radix") (s "remaining"))/2,
          2*((frame (s "radix") (s "remaining"))%2),0⟩ ∧
      out "program" = s "program" := by
  refine ⟨output s,candidate_setup_exact s hradix,?_,?_,?_⟩ <;>
    simp [output,put]

/-- With radix zero the source would enter negative Python integers; the
partial natural semantics stops at the underflow instead of asserting the
incorrect saturated result. This case is unreachable in the real controller. -/
theorem candidate_setup_zero_radix_rejected (s : Store) (hz : s "radix" = 0) :
    candidateSetup s = none := by
  simp [candidateSetup,Shared.PNP.Record285.PythonSyntax.lines16,
    Shared.PNP.Record285.PythonSyntax.lines17,Shared.PNP.Record285.PythonSyntax.lines18,
    sequence,simple,eval,op,augOp,ifOne,put,hz]

end Shared.PNP.Record285.PythonCandidateSetup

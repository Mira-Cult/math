import PASoundness.PAtoCompactFirstFactorFrameRebase
import PASoundness.PAtoCompactFirstFactorFrameEncoding
import PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind

/-! Rebind the single retained output in a supplied high-base frame and then
reallocate it to the caller's target base. This is a conditional proof-data
transformer, not an unconditional successor axiom. -/
namespace PASoundness.PAtoCompactFirstFactorFrameFinalize

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFirstFactorRenameSyntax PASoundness.PAtoCompactFirstFactorFrameRebase
open PASoundness.PAtoCompactFirstFactorFrameEncoding PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Given a finite K frame proof at base a, first change its bound output from
old to out, then move all private relation blocks to base b. The four input
labels may alias. Both output names avoid the three inputs occurring in the
output body; their assigned values may still coincide. The raw successor test
name w is unchanged. -/
def finalize (a b old out w x y p s : Nat)
    (hold : old < a) (houta : out < a+2)
    (holdp : old ≠ p) (holdy : old ≠ y) (holds : old ≠ s)
    (houtp : out ≠ p) (houty : out ≠ y) (houts : out ≠ s)
    (hxa : x < a+2) (hya : y < a+2) (hpa : p < a+2) (hsa : s < a+2)
    (hxb : x < b+2) (hyb : y < b+2) (hpb : p < b+2) (hsb : s < b+2) (houtb : out < b+2)
    (d : KDerivation (assignedFrame a old w x y p s).encode) :
    KDerivation (assignedFrame b out w x y p s).encode := by
  have hnum := to_numeric a old w x y p s d
  have hrenamed := rebind_output a x y p s old out w hold houta holdp holdy holds
    houtp houty houts hnum
  have hnamed := to_named a out w x y p s hrenamed
  exact frame_rebase a b out w x y p s hxa hya hpa hsa houta
    hxb hyb hpb hsb houtb hnamed

theorem finalize_certificate (a b old out w x y p s : Nat)
    (hold : old < a) (houta : out < a+2)
    (holdp : old ≠ p) (holdy : old ≠ y) (holds : old ≠ s)
    (houtp : out ≠ p) (houty : out ≠ y) (houts : out ≠ s)
    (hxa : x < a+2) (hya : y < a+2) (hpa : p < a+2) (hsa : s < a+2)
    (hxb : x < b+2) (hyb : y < b+2) (hpb : p < b+2) (hsb : s < b+2) (houtb : out < b+2)
    (d : KDerivation (assignedFrame a old w x y p s).encode) :
    theoremCode (certificate (finalize a b old out w x y p s hold houta holdp holdy holds
      houtp houty houts hxa hya hpa hsa hxb hyb hpb hsb houtb d)) =
      (assignedFrame b out w x y p s).encode := certificate_correct _

end PASoundness.PAtoCompactFirstFactorFrameFinalize

#print axioms PASoundness.PAtoCompactFirstFactorFrameFinalize.finalize
#print axioms PASoundness.PAtoCompactFirstFactorFrameFinalize.finalize_certificate

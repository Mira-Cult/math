import PASoundness.PAtoCompactCandidateRestrictedInduction
import PASoundness.PAtoCompactInductionJointNumericAllocation
import PASoundness.PAtoCompactInductionJointSelectorFreshness

/-! The restricted candidate-induction engine at the shared concrete numeric
allocation. This constructs the actual finite K engine proof from explicit
source-name and bound conditions; it does not by itself translate PA induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionJointEngineProof
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactCandidateRestrictedInduction
open PASoundness.PAtoCompactInductionJointNumericAllocation PASoundness.PAtoCompactInductionJointSelectorFreshness

/-- Construct the literal restricted engine at the joint offsets. The only
formula-specific assumptions are the explicitly displayed names and bounds. -/
def joint_engine (N B : Nat) (f : Formula)
    (hB : N+101 < B) (hf : f.names.sup id < B)
    (hmf : N+100 ∉ f.names) (hvf : N+1 ∉ f.names)
    (hxf : N+2 ∉ f.names) (htf : N+101 ∉ f.binders) :
    let X := N+2
    let m := N+100
    let v := N+1
    let t := N+101
    let Y := B+100
    let bD := B+6
    let p := B+7
    let q := B+8
    let u := B+12
    let r := B+13
    let l := B+15
    let w := B+24
    KDerivation (imp (candidateCode X bD p q u t l m r)
      (imp (uniformBaseCode t m (B+3) f)
        (imp (allCode Y (imp (candidateCode Y bD p q u t l m r)
          (allStepsCode Y t v m w p q f)))
          (replace t X f).encode))) := by
  dsimp only
  have hnum := joint_numeric_freshness N B (N+2) rfl hB
  dsimp only at hnum
  rcases hnum with ⟨_, _, _, _, _, _, _, _, hn1, hn2, hn3, hn4, hn5, hn6,
    _, _, _, _, _, _, _⟩
  have hsel := joint_selector_context_freshness N B f hB hf hmf
  dsimp only at hsel
  rcases hsel with ⟨hcOthers, hcf, hvc, hrc, hmGraph, hcBase, hcStep,
    hcClass, hYBase, hYInst, hWc, hYc⟩
  have hxbind : N+2 ∉ f.binders := fun h => hxf (f.binders_subset_names h)
  apply candidate_restricted_induction
    (N+2) (B+100) (N+101) (B+12) (B+15) (N+1) (N+100) (B+13)
    (B+3) (B+24) (B+7) (B+8) (B+20) (B+21) (B+6) (B+22) (B+23)
    (B+5) (B+9) (B+10) (B+11) (B+14) (B+16) (B+17) (B+18) (B+19) (B+101) f
  all_goals first | assumption | omega
end PASoundness.PAtoCompactInductionJointEngineProof

#print axioms PASoundness.PAtoCompactInductionJointEngineProof.joint_engine

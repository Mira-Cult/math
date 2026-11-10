import PASoundness.PAtoCompactPAAddSuccFixedAllocated
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactZeroSuccessor

/-! Finite K addition-successor compatibility at fixed names and a uniform
candidate/addition allocation base. The two successor relations remain raw,
with their indicated test name. This is not a PA-axiom translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccUniformBase
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactPAAddSuccFixedAllocated
open PASoundness.PAtoCompactAdditionSuccessorLocalStep PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The fixed operand-name step, with the two candidate assumptions rebased
from 100 to the addition allocation `b`. The actual represented inputs may
coincide even though these syntactic names are distinct. -/
noncomputable def uniform_base_step (b : Nat) (hb : 46 ≤ b) :
    KDerivation (imp (domainAt b 31).encode (imp (domainAt b 32).encode
      (imp (successorCode 31 38 39) (imp (successorCode 32 45 39)
        (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode))))) := by
  have hd31 := domainAt_transport b 100 31 (by omega) (by decide)
  have hd32 := domainAt_transport b 100 32 (by omega) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (addAt b 30 31 32).encode
  let S := successorCode 31 38 39
  let T := successorCode 32 45 39
  let D := (domainAt b 31).encode
  let E := (domainAt b 32).encode
  let Γ := [A,T,S,E,D]
  have hA : Context Γ A := .head _ _
  have hT : Context Γ T := .hypothesis (by simp [Γ])
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hD' : Context Γ (domainAt 100 31).encode := .mp hD (.closed hd31)
  have hE' : Context Γ (domainAt 100 32).encode := .mp hE (.closed hd32)
  have hP : Context Γ fixedAssumptions.encode := by
    have h := Context.conjunctionIntro hD' (Context.conjunctionIntro hE'
      (Context.conjunctionIntro hS hT))
    simpa [fixedAssumptions, namedBoth, namedEither, namedSuccessor, namedSuccessorBody,
      successorCode, S, T, Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  exact .mp hA (.mp hP (.closed (fixed_allocated_step b hb)))

theorem uniform_base_step_certificate (b : Nat) (hb : 46 ≤ b) :
    theoremCode (certificate (uniform_base_step b hb)) =
      imp (domainAt b 31).encode (imp (domainAt b 32).encode
        (imp (successorCode 31 38 39) (imp (successorCode 32 45 39)
          (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode)))) :=
  certificate_correct _
end PASoundness.PAtoCompactPAAddSuccUniformBase
#print axioms PASoundness.PAtoCompactPAAddSuccUniformBase.uniform_base_step
#print axioms PASoundness.PAtoCompactPAAddSuccUniformBase.uniform_base_step_certificate

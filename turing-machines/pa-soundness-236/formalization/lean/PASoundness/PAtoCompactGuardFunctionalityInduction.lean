import PASoundness.PAtoCompactFullTermTotalityInduction
import PASoundness.PAtoCompactGuardedUnaryOutput
import PASoundness.PAtoCompactMulGuardFunctionalityStep
import PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

/-! Structural recursion for guarded graph functionality of PA terms.
The successor and addition node constructors remain explicit inputs; the
multiplication node uses the separately established guarded constructor.
This module does not establish either input or output transport. -/

namespace PASoundness.PAtoCompactGuardFunctionalityInduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedUnaryOutput
open PASoundness.PAtoCompactFullTermTotalityInduction
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

/-- The two node proof families not supplied by this structural recursion. -/
structure NodeSteps where
  successor : ∀ (g : Formula) (t : Peano.Term), GuardFunctionality g t →
    GuardFunctionality g (Peano.succ t)
  addition : ∀ (g : Formula) (t u : Peano.Term), GuardFunctionality g t →
    GuardFunctionality g u → GuardFunctionality g (Peano.add t u)

/-- A given arithmetic syntax tree yields its guarded graph-functionality
family from the two displayed node inputs. Variable and zero functionality
and the multiplication step use finite K proof constructors. -/
noncomputable def functional (steps : NodeSteps) (g : Formula)
    {t : Peano.Term} (h : FullArithmeticTerm t) : GuardFunctionality g t := by
  induction h with
  | var a => exact unary_functionality g (UnaryTerm.var a)
  | zero => exact unary_functionality g UnaryTerm.zero
  | @succ t ht ih => exact steps.successor g t ih
  | @add t u ht hu iht ihu => exact steps.addition g t u iht ihu
  | @mul t u ht hu iht ihu =>
      simpa [binaryTerm, Peano.mul] using
        PASoundness.PAtoCompactMulGuardFunctionalityStep.mul_guard_functionality g t u iht ihu

/-- All PA terms have guarded graph functionality provided the explicit
successor and addition node families are supplied. -/
noncomputable def uniform (steps : NodeSteps) : UniformFunctionality :=
  fun g t => functional steps g (allTerms t)

/-- The structural recursion exposes a certificate for every resulting K
proof at the caller's allocation and guard premises. -/
theorem uniform_certificate (steps : NodeSteps) (g : Formula) (t : Peano.Term)
    (b p q : Nat) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) :
    theoremCode (certificate (uniform steps g t b p q hp hq ht hg hd)) =
      imp g.encode (imp (termGraph id t p b).encode
        (imp (termGraph id t q b).encode (equivAt b p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactGuardFunctionalityInduction

#print axioms PASoundness.PAtoCompactGuardFunctionalityInduction.NodeSteps
#print axioms PASoundness.PAtoCompactGuardFunctionalityInduction.functional
#print axioms PASoundness.PAtoCompactGuardFunctionalityInduction.uniform
#print axioms PASoundness.PAtoCompactGuardFunctionalityInduction.uniform_certificate

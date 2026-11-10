import PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
import PASoundness.PAtoCompactFullTermTotalityInduction
import PASoundness.PAtoCompactGuardedUnaryOutput

/-! Reduce uniform guarded output transport to the two binary-root families.
The addition and multiplication families are explicit finite-K proof inputs;
this module does not construct them or assert unconditional uniform transport. -/

namespace PASoundness.PAtoCompactUniformOutputFromBinaryRoots

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFullTermTotalityInduction
open PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactZeroGraphOutputTransport
open PASoundness.PAtoCompactSuccGraphOutputClosed
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

/-- The two outstanding output-transport families, each for all guards and
arbitrary operand terms. No graph functionality or child proofs are implicit. -/
structure BinaryRootOutput where
  addition : ∀ (g : Formula) (t u : Peano.Term),
    GuardedOutputTransport g (Peano.add t u)
  multiplication : ∀ (g : Formula) (t u : Peano.Term),
    GuardedOutputTransport g (Peano.mul t u)

/-- Match on a PA-term shape. For successor the tracked relation proof works
for an arbitrary child and does not consume a child output-transport proof. -/
noncomputable def from_shape (roots : BinaryRootOutput) (g : Formula)
    {t : Peano.Term} (shape : FullArithmeticTerm t) : GuardedOutputTransport g t := by
  cases shape with
  | var a => exact variable_output g a
  | zero =>
      apply guard_unguarded_output
      intro b q r hq hr _
      exact zero_graph_output id b q r hq hr
  | @succ u hu =>
      apply guard_unguarded_output
      intro b q r hq hr hv
      have hvars : ∀ a ∈ u.varFinset, id a < b := by
        intro a ha
        apply hv a
        simp [Term.varFinset, ha]
      exact succ_graph_output id u b q r hq hr hvars
  | @add t u ht hu => exact roots.addition g t u
  | @mul t u ht hu => exact roots.multiplication g t u

/-- Explicit addition- and multiplication-root inputs construct the full
uniform output family for every guard and PA term. This is a noncomputable
proof-data transformer, not an unconditional graph theorem. -/
noncomputable def uniform_output (roots : BinaryRootOutput) : UniformOutput := by
  intro g t
  exact from_shape roots g (allTerms t)

/-- The constructed family produces a certificate of the exact guarded output
implication when all naming and guard-candidate premises are supplied. -/
theorem uniform_output_certificate (roots : BinaryRootOutput) (g : Formula)
    (t : Peano.Term) (b q r : Nat) (hq : q < b) (hr : r < b)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode)) :
    theoremCode (certificate (uniform_output roots g t b q r hq hr ht hg hd)) =
      imp g.encode (imp (domainAt b r).encode
        (imp (termGraph id t q b).encode
          (imp (equivAt b q r).encode (termGraph id t r b).encode))) := certificate_correct _

end PASoundness.PAtoCompactUniformOutputFromBinaryRoots

#print axioms PASoundness.PAtoCompactUniformOutputFromBinaryRoots.BinaryRootOutput
#print axioms PASoundness.PAtoCompactUniformOutputFromBinaryRoots.from_shape
#print axioms PASoundness.PAtoCompactUniformOutputFromBinaryRoots.uniform_output
#print axioms PASoundness.PAtoCompactUniformOutputFromBinaryRoots.uniform_output_certificate

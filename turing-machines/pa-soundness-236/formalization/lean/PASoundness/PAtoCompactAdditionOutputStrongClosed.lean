import PASoundness.PAtoCompactAdditionMemberPointStrong

/-! Compose the equal-cut and member-cut finite-K constructions under the
explicit four operand/output candidate-domain guards. This is a fixed-label,
noncomputable proof-data construction, not yet the uniform term-graph law. -/
namespace PASoundness.PAtoCompactAdditionOutputStrongClosed
open PASoundness.CompactProof
open PASoundness.PAtoCompactAdditionOutputStrongCases PASoundness.PAtoCompactAdditionMemberPointStrong
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the explicit strong target guards, literal addition at output 32
transports to allocated addition at output 8. Both cut cases are handled by
K proof data; the source term-graph and arbitrary-label adapters are separate. -/
noncomputable def addition_output_strong : KDerivation
    (imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode strongTarget.encode) :=
  addition_output_of_member_point_strong member_point_strong

theorem addition_output_strong_certificate : theoremCode (certificate addition_output_strong) =
    imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode strongTarget.encode :=
  certificate_correct addition_output_strong
end PASoundness.PAtoCompactAdditionOutputStrongClosed

#print axioms PASoundness.PAtoCompactAdditionOutputStrongClosed.addition_output_strong
#print axioms PASoundness.PAtoCompactAdditionOutputStrongClosed.addition_output_strong_certificate

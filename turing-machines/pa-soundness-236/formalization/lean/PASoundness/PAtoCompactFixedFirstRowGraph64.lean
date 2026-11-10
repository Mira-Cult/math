import PASoundness.PAtoCompactFixedFirstRowSuffixTarget40

/-! Capture-safe alpha conversion of the collected row-graph witness from
name 7 to name 64. The suffix map graph remains at its original name 6. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFixedFirstPreservedBase PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactFixedFirstRowSuffixTarget40

/-- Full-source invariant with the original graph witness name 7. -/
def rowBody7 : Formula := replace 0 31 (rowInvariantPreserved 7)

/-- The very same full-source invariant, with its graph parameter at name 64. -/
def rowBody64 : Formula := replace 7 64 rowBody7

/-- The suffix graph name 6 and other parameters are retained unchanged. -/
theorem row_body64_shape : rowBody64 = replace 0 31 (rowInvariantPreserved 64) := by decide

/-- Rebinding the existential changes only its graph witness name. -/
def row_graph_alpha : KDerivation
    (imp (replace 0 31 predicate).encode (existsCode 64 rowBody64.encode)) := by
  have h := (existentialAlpha 7 64 rowBody7 (by decide) (by decide) (by decide)).1
  have he : replace 0 31 predicate = .ex 7 rowBody7 := by decide
  rw [he]
  simpa [rowBody64, Formula.encode] using h

theorem row_graph_alpha_certificate : theoremCode (certificate row_graph_alpha) =
    imp (replace 0 31 predicate).encode (existsCode 64 rowBody64.encode) := certificate_correct _

/-- A candidate source and a supplied source31-to-suffix40 bijection construct
one row witness at name 64 while retaining the same map graph 6. -/
def row_exists_graph64 : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection40.encode (existsCode 64 rowBody64.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [mapBijection40.encode,candidateCode 31 213 209 210 202 0 203 205 206]
  have hm : Context Γ mapBijection40.encode := .head _ _
  have hc : Context Γ (candidateCode 31 213 209 210 202 0 203 205 206) :=
    .hypothesis (by simp [Γ])
  exact .mp (.mp hm (.mp hc (.closed row_exists_at_40))) (.closed row_graph_alpha)

theorem row_exists_graph64_certificate : theoremCode (certificate row_exists_graph64) =
    imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection40.encode (existsCode 64 rowBody64.encode)) := certificate_correct _
end PASoundness.PAtoCompactFixedFirstRowGraph64
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.rowBody7
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.rowBody64
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.row_body64_shape
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.row_graph_alpha
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.row_graph_alpha_certificate
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.row_exists_graph64
#print axioms PASoundness.PAtoCompactFixedFirstRowGraph64.row_exists_graph64_certificate

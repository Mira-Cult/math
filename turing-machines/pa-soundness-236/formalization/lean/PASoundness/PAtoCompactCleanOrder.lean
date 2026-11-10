import PASoundness.PAtoCompactCleanOrderAlpha
import PASoundness.PAtoCompactCleanOrderPoint
import PASoundness.PAtoCompactCleanBijectionInstance
import PASoundness.PAtoCompactCleanGuardInstances

/-! Transfer the exact K order matrix between two supplied graphs under
explicit guarded edge equivalence. This does not construct a filter, a
represented graph, a quotient, or a PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrderIsoInstance PASoundness.PAtoCompactCleanMatrixData
open PASoundness.PAtoCompactCleanOrderAlpha PASoundness.PAtoCompactCleanOrderPoint
open PASoundness.PAtoCompactCleanBijectionInstance PASoundness.PAtoCompactCleanGuardInstances

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Capture-safe instantiation of the exact old graph-10 order clause. -/
def old_order_instance : KDerivation (imp oldOrder10.encode oldOrderMatrix10.encode) := by
  have h₂ := allSpecialize 2 (.all 4 (.all 3 (.all 5 oldOrderMatrix10))) (by decide)
  have h₄ := allSpecialize 4 (.all 3 (.all 5 oldOrderMatrix10)) (by decide)
  have h₃ := allSpecialize 3 (.all 5 oldOrderMatrix10) (by decide)
  have h₅ := allSpecialize 5 oldOrderMatrix10 (by decide)
  rw [old_order_shape]
  exact compose h₂ (compose h₄ (compose h₃ h₅))

/-- The old graph-10 pointwise matrix has exactly the guards and comparison
used by the supplied pointwise transfer theorem. -/
theorem old_matrix_shape : oldOrderMatrix10.encode = imp oldA comparison := by rfl

/-- The graph-6 pointwise matrix has exactly the guards and comparison used
by the supplied pointwise transfer theorem. -/
theorem new_matrix_shape : orderMatrix.encode = imp newA comparison := by rfl

/-- Both hypotheses are provably vacuous at each order point label. -/
def context_vacuity (x : Nat) (hx : x ∈ [2,4,3,5]) :
    ∀ h, h ∈ [oldOrderFresh.encode,guardedEdges.encode] →
      KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  by_cases he : h = oldOrderFresh.encode
  · subst h
    exact order_vacuity x hx
  · have he' : h = guardedEdges.encode := hh.resolve_left he
    subst h
    apply guardedEdges.vacuity
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- Under a supplied uniform guarded edge comparison and alpha-freshened old
order clause, derive the exact graph-6 order clause. -/
def order_from_fresh : KDerivation
    (imp guardedEdges.encode (imp oldOrderFresh.encode orderFormula.encode)) := by
  let Γ := [oldOrderFresh.encode,guardedEdges.encode]
  have hG : Context Γ guardedEdges.encode := .hypothesis (by simp [Γ])
  have hO : Context Γ oldOrderFresh.encode := Context.head _ _
  have h23 : KDerivation guard23 := instance_23
  have h45 : KDerivation guard45 := instance_45
  have ho : Context Γ oldOrder10.encode := .mp hO (.closed order_unalpha)
  have hpointOld : Context Γ (imp oldA comparison) := by
    have h := Context.mp ho (.closed old_order_instance)
    simpa only [old_matrix_shape] using h
  have hpointNew : Context Γ orderMatrix.encode := by
    have h := Context.mp hpointOld (.mp hG (.closed (point_transfer h23 h45)))
    simpa only [new_matrix_shape] using h
  have h5 := Context.generalize 5 (context_vacuity 5 (by decide)) hpointNew
  have h3 := Context.generalize 3 (context_vacuity 3 (by decide)) h5
  have h4 := Context.generalize 4 (context_vacuity 4 (by decide)) h3
  have h2 := Context.generalize 2 (context_vacuity 2 (by decide)) h4
  have horder : Context Γ orderFormula.encode := by
    change Context Γ (Formula.all 2 (.all 4 (.all 3 (.all 5 orderMatrix)))).encode
    exact h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact horder

/-- Exact graph-10 to graph-6 order transfer, conditional on guarded edge
comparison and the supplied old matrix. -/
def clean_order_transfer : KDerivation
    (imp guardedEdges.encode (imp oldMatrix10.encode orderFormula.encode)) := by
  let Γ := [oldMatrix10.encode,guardedEdges.encode]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hG : Context Γ guardedEdges.encode := .hypothesis (by simp [Γ])
  have hM : Context Γ oldMatrix10.encode := Context.head _ _
  have hO : Context Γ oldOrder10.encode := by
    rw [PAtoCompactCleanOrderAlpha.old_matrix_shape] at hM
    exact Context.conjunctionRight hM
  have hF : Context Γ oldOrderFresh.encode := .mp hO (.closed order_alpha)
  exact .mp hF (.mp hG (.closed order_from_fresh))

theorem clean_order_transfer_certificate : theoremCode (certificate clean_order_transfer) =
    imp guardedEdges.encode (imp oldMatrix10.encode orderFormula.encode) :=
  certificate_correct clean_order_transfer

end PASoundness.PAtoCompactCleanOrder

#print axioms PASoundness.PAtoCompactCleanOrder.clean_order_transfer
#print axioms PASoundness.PAtoCompactCleanOrder.clean_order_transfer_certificate

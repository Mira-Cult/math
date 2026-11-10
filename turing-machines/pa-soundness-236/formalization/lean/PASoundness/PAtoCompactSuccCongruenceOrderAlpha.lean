import PASoundness.PAtoCompactOrderIsoInstance

/-! Rename the exact old order clause's four quantifier labels away from the
new order clause's point names. These are finite K alpha-conversion proofs;
they do not establish order preservation, graph existence or a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceOrderAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance

/-- Successive capture-safe renamings of the exact old order matrix. -/
def M2 : Formula := replace 2 30 orderMatrix
def M4 : Formula := replace 4 31 M2
def M3 : Formula := replace 3 32 M4
def M5 : Formula := replace 5 33 M3

def R2 : Formula := .all 30 (.all 4 (.all 3 (.all 5 M2)))
def R4 : Formula := .all 30 (.all 31 (.all 3 (.all 5 M4)))
def R3 : Formula := .all 30 (.all 31 (.all 32 (.all 5 M3)))
def oldOrderFresh : Formula := .all 30 (.all 31 (.all 32 (.all 33 M5)))

/-- The literal old order clause entails its alpha-renamed copy. -/
def order_alpha : KDerivation (imp orderFormula.encode oldOrderFresh.encode) := by
  let F2 : Formula := .all 4 (.all 3 (.all 5 orderMatrix))
  have h2 := (universalAlpha 2 30 F2 (by decide) (by decide) (by decide)).1
  have he2 : replace 2 30 F2 = .all 4 (.all 3 (.all 5 M2)) := by decide
  rw [he2] at h2
  have h2' : KDerivation (imp orderFormula.encode R2.encode) := by
    simpa [orderFormula, orderMatrix, F2, R2, Formula.encode] using h2
  let F4 : Formula := .all 3 (.all 5 M2)
  have h4 := (universalAlpha 4 31 F4 (by decide) (by decide) (by decide)).1
  have he4 : replace 4 31 F4 = .all 3 (.all 5 M4) := by decide
  rw [he4] at h4
  have h4' : KDerivation (imp R2.encode R4.encode) := by
    simpa [F4, R2, R4, Formula.encode] using allCongr 30 h4
  let F3 : Formula := .all 5 M4
  have h3 := (universalAlpha 3 32 F3 (by decide) (by decide) (by decide)).1
  have he3 : replace 3 32 F3 = .all 5 M3 := by decide
  rw [he3] at h3
  have h3' : KDerivation (imp R4.encode R3.encode) := by
    simpa [F3, R4, R3, Formula.encode] using allCongr 30 (allCongr 31 h3)
  have h5 := (universalAlpha 5 33 M3 (by decide) (by decide) (by decide)).1
  have he5 : replace 5 33 M3 = M5 := rfl
  rw [he5] at h5
  have h5' : KDerivation (imp R3.encode oldOrderFresh.encode) := by
    simpa [R3, oldOrderFresh, Formula.encode] using allCongr 30 (allCongr 31 (allCongr 32 h5))
  exact compose h2' (compose h4' (compose h3' h5'))

/-- The alpha-renamed copy entails the original exact order clause. -/
def order_unalpha : KDerivation (imp oldOrderFresh.encode orderFormula.encode) := by
  let F2 : Formula := .all 4 (.all 3 (.all 5 orderMatrix))
  have h2 := (universalAlpha 2 30 F2 (by decide) (by decide) (by decide)).2
  have he2 : replace 2 30 F2 = .all 4 (.all 3 (.all 5 M2)) := by decide
  rw [he2] at h2
  have h2' : KDerivation (imp R2.encode orderFormula.encode) := by
    simpa [orderFormula, orderMatrix, F2, R2, Formula.encode] using h2
  let F4 : Formula := .all 3 (.all 5 M2)
  have h4 := (universalAlpha 4 31 F4 (by decide) (by decide) (by decide)).2
  have he4 : replace 4 31 F4 = .all 3 (.all 5 M4) := by decide
  rw [he4] at h4
  have h4' : KDerivation (imp R4.encode R2.encode) := by
    simpa [F4, R2, R4, Formula.encode] using allCongr 30 h4
  let F3 : Formula := .all 5 M4
  have h3 := (universalAlpha 3 32 F3 (by decide) (by decide) (by decide)).2
  have he3 : replace 3 32 F3 = .all 5 M3 := by decide
  rw [he3] at h3
  have h3' : KDerivation (imp R3.encode R4.encode) := by
    simpa [F3, R4, R3, Formula.encode] using allCongr 30 (allCongr 31 h3)
  have h5 := (universalAlpha 5 33 M3 (by decide) (by decide) (by decide)).2
  have he5 : replace 5 33 M3 = M5 := rfl
  rw [he5] at h5
  have h5' : KDerivation (imp oldOrderFresh.encode R3.encode) := by
    simpa [R3, oldOrderFresh, Formula.encode] using allCongr 30 (allCongr 31 (allCongr 32 h5))
  exact compose h5' (compose h3' (compose h4' h2'))

/-- The freshened order hypothesis can be generalized over any of the new
order clause's four point labels without capture. -/
def order_vacuity (x : Nat) (hx : x ∈ [2,4,3,5]) :
    KDerivation (imp oldOrderFresh.encode (allCode x oldOrderFresh.encode)) := by
  apply oldOrderFresh.vacuity
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem order_alpha_certificate : theoremCode (certificate order_alpha) =
    imp orderFormula.encode oldOrderFresh.encode := certificate_correct order_alpha

theorem order_unalpha_certificate : theoremCode (certificate order_unalpha) =
    imp oldOrderFresh.encode orderFormula.encode := certificate_correct order_unalpha

end PASoundness.PAtoCompactSuccCongruenceOrderAlpha

#print axioms PASoundness.PAtoCompactSuccCongruenceOrderAlpha.order_alpha
#print axioms PASoundness.PAtoCompactSuccCongruenceOrderAlpha.order_unalpha
#print axioms PASoundness.PAtoCompactSuccCongruenceOrderAlpha.order_vacuity
#print axioms PASoundness.PAtoCompactSuccCongruenceOrderAlpha.order_alpha_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceOrderAlpha.order_unalpha_certificate

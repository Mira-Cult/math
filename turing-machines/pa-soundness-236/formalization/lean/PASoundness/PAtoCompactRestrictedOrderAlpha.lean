import PASoundness.PAtoCompactRestrictedOrderAll
import PASoundness.CompactFreshen

/-! Capture-safe naming of the restricted order matrix. The alpha conversions
are actual bidirectional K proof data. Free-name replacement is recorded as
syntax, not asserted to preserve arbitrary K derivability. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedOrderAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactRestrictedOrderAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def b30 : Formula := replace 2 30 orderMatrix
private def b31 : Formula := replace 4 31 b30
private def b32 : Formula := replace 3 32 b31
private def b33 : Formula := replace 5 33 b32

/-- The canonical order clause after alpha-renaming its four coordinate
binders away from the intended endpoint and graph names. -/
def alphaOrder : Formula := .all 30 (.all 31 (.all 32 (.all 33 b33)))

/-- Finite K proofs in both directions of the capture-safe coordinate-binder
renaming. The free source, target and graph names are still 0,1,6. -/
def order_alpha : ProofEquiv orderFormula alphaOrder := by
  let b := orderMatrix
  have h1 := ProofEquiv.alphaAll 2 30 (.all 4 (.all 3 (.all 5 b)))
    (by decide) (by decide) (by decide)
  have e1 : replace 2 30 (.all 4 (.all 3 (.all 5 b))) = .all 4 (.all 3 (.all 5 b30)) := by decide
  rw [e1] at h1
  have h2 := ProofEquiv.universal 30 (ProofEquiv.alphaAll 4 31 (.all 3 (.all 5 b30))
    (by decide) (by decide) (by decide))
  have e2 : replace 4 31 (.all 3 (.all 5 b30)) = .all 3 (.all 5 b31) := by decide
  rw [e2] at h2
  have h3 := ProofEquiv.universal 30 (ProofEquiv.universal 31
    (ProofEquiv.alphaAll 3 32 (.all 5 b31) (by decide) (by decide) (by decide)))
  have e3 : replace 3 32 (.all 5 b31) = .all 5 b32 := by decide
  rw [e3] at h3
  have h4 := ProofEquiv.universal 30 (ProofEquiv.universal 31 (ProofEquiv.universal 32
    (ProofEquiv.alphaAll 5 33 b32 (by decide) (by decide) (by decide))))
  have e4 : replace 5 33 b32 = b33 := by decide
  rw [e4] at h4
  have h := h1.trans (h2.trans (h3.trans h4))
  simpa only [b, orderFormula, orderMatrix, alphaOrder] using h

/-- Free-name replacement is performed only after the binder conversion:
source 0 becomes 2, target 1 becomes 5, and graph 6 becomes 8. -/
def renamedOrder : Formula := replace 6 8 (replace 1 5 (replace 0 2 alphaOrder))

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)
private def namedRestricted : Formula := .all 30 (.all 31 (.all 32 (.all 33
  (.imp (conj (.member 2 30) (conj (.member 2 31)
    (conj (.member 5 32) (conj (.member 5 33)
      (conj (graphFormula 8 30 32) (graphFormula 8 31 33))))))
    (iff' (.member 31 30) (.member 33 32))))))

/-- The separately constructed quantified old-domain matrix is literally
the code of that capture-safe named formula. -/
theorem renamed_order_code : renamedOrder.encode = restrictedOrder := by
  have hn : renamedOrder = namedRestricted := by decide
  rw [hn]
  rfl

/-- The preceding syntactic identity gives actual K proof data in both
directions between the named restricted matrix and its numeric source. -/
def restricted_order_identity : KDerivation (imp renamedOrder.encode restrictedOrder) := by
  rw [← renamed_order_code]
  exact CompactHilbertBasis.identity _

def restricted_order_identity_reverse : KDerivation (imp restrictedOrder renamedOrder.encode) := by
  rw [← renamed_order_code]
  exact CompactHilbertBasis.identity _

end PASoundness.PAtoCompactRestrictedOrderAlpha

#print axioms PASoundness.PAtoCompactRestrictedOrderAlpha.order_alpha
#print axioms PASoundness.PAtoCompactRestrictedOrderAlpha.renamed_order_code
#print axioms PASoundness.PAtoCompactRestrictedOrderAlpha.restricted_order_identity
#print axioms PASoundness.PAtoCompactRestrictedOrderAlpha.restricted_order_identity_reverse

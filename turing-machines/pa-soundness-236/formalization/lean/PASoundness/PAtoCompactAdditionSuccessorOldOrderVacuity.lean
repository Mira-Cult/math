import PASoundness.PAtoCompactAdditionSuccessorOldOld
import PASoundness.CompactFreshen

/-! Explicit K vacuity for the original old-order formula at point labels
2–5. Its quantifiers bind those labels, so syntactic absence fails; freshening
all internal binders above 60 preserves the literal formula up to proved K
alpha equivalence. No arithmetic or order-existence claim is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdditionSuccessorOldOld
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private theorem names_lt : ∀ v ∈ oldOrder.names, v < 60 := by
  intro v hv
  have h := Finset.le_sup (f := id) hv
  change v ≤ oldOrder.names.sup id at h
  have h' : oldOrder.names.sup id < 60 := by decide
  omega
private def freshOrder := freshen oldOrder 60 names_lt
private theorem fresh2 : 2 ∉ freshOrder.formula.names := by decide
private theorem fresh3 : 3 ∉ freshOrder.formula.names := by decide
private theorem fresh4 : 4 ∉ freshOrder.formula.names := by decide
private theorem fresh5 : 5 ∉ freshOrder.formula.names := by decide

private def vacuity (v : Nat) (h : v ∉ freshOrder.formula.names) :
    KDerivation (imp oldOrder.encode (allCode v oldOrder.encode)) :=
  compose freshOrder.equivalent.forward
    (compose (freshOrder.formula.vacuity v h) (allCongr v freshOrder.equivalent.backward))

def old_order_vacuity2 : KDerivation (imp oldOrder.encode (allCode 2 oldOrder.encode)) := vacuity 2 fresh2
def old_order_vacuity3 : KDerivation (imp oldOrder.encode (allCode 3 oldOrder.encode)) := vacuity 3 fresh3
def old_order_vacuity4 : KDerivation (imp oldOrder.encode (allCode 4 oldOrder.encode)) := vacuity 4 fresh4
def old_order_vacuity5 : KDerivation (imp oldOrder.encode (allCode 5 oldOrder.encode)) := vacuity 5 fresh5

theorem vacuity2_certificate : theoremCode (certificate old_order_vacuity2) =
    imp oldOrder.encode (allCode 2 oldOrder.encode) := certificate_correct old_order_vacuity2
theorem vacuity3_certificate : theoremCode (certificate old_order_vacuity3) =
    imp oldOrder.encode (allCode 3 oldOrder.encode) := certificate_correct old_order_vacuity3
theorem vacuity4_certificate : theoremCode (certificate old_order_vacuity4) =
    imp oldOrder.encode (allCode 4 oldOrder.encode) := certificate_correct old_order_vacuity4
theorem vacuity5_certificate : theoremCode (certificate old_order_vacuity5) =
    imp oldOrder.encode (allCode 5 oldOrder.encode) := certificate_correct old_order_vacuity5
end PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.old_order_vacuity2
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.old_order_vacuity3
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.old_order_vacuity4
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.old_order_vacuity5
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.vacuity2_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.vacuity3_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.vacuity4_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity.vacuity5_certificate

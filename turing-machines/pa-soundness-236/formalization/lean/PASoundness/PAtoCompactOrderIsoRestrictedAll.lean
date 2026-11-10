import PASoundness.PAtoCompactOrderIsoRestrictedGuard
import PASoundness.PAtoCompactOrderIsoRestrictedGlobal
import PASoundness.PAtoCompactOrderIsoVacuity
import PASoundness.PAtoCompactOrderIsoInstance
import PASoundness.PAtoCompactOrderIsoReverseInstance

/-! Quantified reverse-order transfer from the exact candidate order clause
under domain-restricted inverse graph correspondence. Existence of a graph,
and full isomorphism symmetry, remain separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoRestrictedAll
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactOrderIsoRestrictedGlobal PASoundness.PAtoCompactOrderIsoRestrictedGuard
open PASoundness.PAtoCompactOrderIsoVacuity PASoundness.PAtoCompactOrderIsoReverseInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def restrictedReverseOrderAll : Nat := allCode 3 (allCode 5 (allCode 2 (allCode 4 reverseMatrix)))

/-- The restricted inverse family and the candidate's forward order clause
yield all reversed guarded order instances. -/
def restricted_reverse_order_all : KDerivation
    (imp restrictedFamily.encode (imp orderFormula.encode restrictedReverseOrderAll)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [orderFormula.encode,restrictedFamily.encode]
  have ho : Context Γ orderFormula.encode := Context.head _ _
  have hr : Context Γ restrictedFamily.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (both atFirst.encode atSecond.encode) :=
    .mp hr (.closed restricted_instances)
  have hi₁ := Context.conjunctionLeft he
  have hi₂ := Context.conjunctionRight he
  have hm : Context Γ orderMatrix.encode := .mp ho (.closed order_instance)
  have ht : Context Γ (imp atFirst.encode (imp atSecond.encode (imp orderMatrix.encode reverseMatrix))) :=
    .closed (restricted_reverse_guarded (member 0 2) (member 0 4) (member 1 3) (member 1 5)
      (graphFormula 6 2 3).encode (graphFormula 6 4 5).encode
      (graphFormula 7 3 2).encode (graphFormula 7 5 4).encode
      (member 4 2) (member 5 3))
  have hl : Context Γ reverseMatrix := .mp hm (.mp hi₂ (.mp hi₁ ht))
  have hv (v : Nat) (a : v ∉ freshOrder.formula.names)
      (b : v ∉ freshFamily.formula.names) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases heq : h = orderFormula.encode
    · subst h
      exact order_vacuity v a
    · have heq' : h = restrictedFamily.encode := hh.resolve_left heq
      subst h
      exact family_vacuity v b
  exact Context.generalize 3 (hv 3 order_fresh_3 fresh_3)
    (Context.generalize 5 (hv 5 order_fresh_5 fresh_5)
      (Context.generalize 2 (hv 2 order_fresh_2 fresh_2)
        (Context.generalize 4 (hv 4 order_fresh_4 fresh_4) hl)))

theorem restricted_reverse_order_all_certificate :
    theoremCode (certificate restricted_reverse_order_all) =
      imp restrictedFamily.encode (imp orderFormula.encode restrictedReverseOrderAll) :=
  certificate_correct restricted_reverse_order_all

end PASoundness.PAtoCompactOrderIsoRestrictedAll

#print axioms PASoundness.PAtoCompactOrderIsoRestrictedAll.restricted_reverse_order_all
#print axioms PASoundness.PAtoCompactOrderIsoRestrictedAll.restricted_reverse_order_all_certificate

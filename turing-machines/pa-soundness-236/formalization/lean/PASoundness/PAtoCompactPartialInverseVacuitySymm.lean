import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactFreshen

/-! Freshness for the concrete no-spurious-edge conclusion. The original
old-graph formula binds name 19, so name-absence is obtained only after
capture-safe freshening with explicit bidirectional K proof data. No semantic
soundness or graph-existence claim is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseVacuitySymm
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Either the old reverse graph has the selected edge, or its coordinates
match the newly added pair. -/
def conclusion : Formula :=
  (graphFormula 7 3 2).not.imp (((Formula.equal 3 13).imp (Formula.equal 2 12).not).not)

private theorem names_lt : ∀ v ∈ conclusion.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ conclusion.names.sup id at hm
  have hb : conclusion.names.sup id < 30 := by decide
  omega

def freshConclusion := freshen conclusion 30 names_lt

theorem binder_fresh : 19 ∉ freshConclusion.formula.names := by decide

/-- The conclusion is vacuous at the selected graph-witness binder 19. This
is a finite proof in K even though the original conclusion binds that name. -/
def conclusion_vacuity : KDerivation (imp conclusion.encode (allCode 19 conclusion.encode)) :=
  compose freshConclusion.equivalent.forward
    (compose (freshConclusion.formula.vacuity 19 binder_fresh)
      (allCongr 19 freshConclusion.equivalent.backward))

theorem conclusion_vacuity_certificate :
    theoremCode (certificate conclusion_vacuity) =
      imp conclusion.encode (allCode 19 conclusion.encode) :=
  certificate_correct conclusion_vacuity

end PASoundness.PAtoCompactPartialInverseVacuitySymm

#print axioms PASoundness.PAtoCompactPartialInverseVacuitySymm.conclusion_vacuity
#print axioms PASoundness.PAtoCompactPartialInverseVacuitySymm.conclusion_vacuity_certificate

import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.PAtoCompactConditionalTransitivityOrderSecond
import PASoundness.CompactFreshen

/-! Literal K vacuity for generalizing the four endpoint coordinates in the
presence of the two source order clauses and the supplied composition premise.
The proofs use capture-safe alpha-freshening, including for names already
bound inside the assumptions. No graph existence or transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityQuantVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem order_names_lt : ∀ v ∈ orderFormula.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ orderFormula.names.sup id at hm
  have hb : orderFormula.names.sup id < 30 := by decide
  omega

private theorem second_names_lt : ∀ v ∈ secondOrder.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ secondOrder.names.sup id at hm
  have hb : secondOrder.names.sup id < 30 := by decide
  omega

private theorem composition_names_lt : ∀ v ∈ composition.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ composition.names.sup id at hm
  have hb : composition.names.sup id < 30 := by decide
  omega

def freshOrder := freshen orderFormula 30 order_names_lt
def freshSecond := freshen secondOrder 30 second_names_lt
def freshComposition := freshen composition 30 composition_names_lt

/-- Vacuity transported through a literal K proof equivalence. -/
private def vacuity_of_equiv (f f' : Formula) (eqv : ProofEquiv f f') (v : Nat)
    (hv : v ∉ f'.names) : KDerivation (imp f.encode (allCode v f.encode)) :=
  compose eqv.forward (compose (f'.vacuity v hv) (allCongr v eqv.backward))

/-- Three context assumptions in the order used by the quantified transfer. -/
def assumptions : List Nat := [composition.encode, secondOrder.encode, orderFormula.encode]

/-- Given explicit freshness in each alpha-freshened assumption, supply the
actual K vacuity derivation required by `Context.generalize`. -/
def context_vacuity (v : Nat)
    (hc : v ∉ freshComposition.formula.names)
    (hs : v ∉ freshSecond.formula.names)
    (ho : v ∉ freshOrder.formula.names) :
    ∀ h, h ∈ assumptions → KDerivation (imp h (allCode v h)) := by
  intro h hh
  by_cases hcomp : h = composition.encode
  · subst h
    exact vacuity_of_equiv composition freshComposition.formula freshComposition.equivalent v hc
  by_cases hsecond : h = secondOrder.encode
  · subst h
    exact vacuity_of_equiv secondOrder freshSecond.formula freshSecond.equivalent v hs
  have horder : h = orderFormula.encode := by
    simpa [assumptions, hcomp, hsecond] using hh
  subst h
  exact vacuity_of_equiv orderFormula freshOrder.formula freshOrder.equivalent v ho

def context_vacuity2 := context_vacuity 2 (by decide) (by decide) (by decide)
def context_vacuity3 := context_vacuity 3 (by decide) (by decide) (by decide)
def context_vacuity4 := context_vacuity 4 (by decide) (by decide) (by decide)
def context_vacuity5 := context_vacuity 5 (by decide) (by decide) (by decide)

theorem context_vacuity2_certificate (h : Nat) (hh : h ∈ assumptions) :
    theoremCode (certificate (context_vacuity2 h hh)) = imp h (allCode 2 h) :=
  certificate_correct (context_vacuity2 h hh)

end PASoundness.PAtoCompactConditionalTransitivityQuantVacuity

#print axioms PASoundness.PAtoCompactConditionalTransitivityQuantVacuity.context_vacuity2
#print axioms PASoundness.PAtoCompactConditionalTransitivityQuantVacuity.context_vacuity3
#print axioms PASoundness.PAtoCompactConditionalTransitivityQuantVacuity.context_vacuity4
#print axioms PASoundness.PAtoCompactConditionalTransitivityQuantVacuity.context_vacuity5
#print axioms PASoundness.PAtoCompactConditionalTransitivityQuantVacuity.context_vacuity2_certificate

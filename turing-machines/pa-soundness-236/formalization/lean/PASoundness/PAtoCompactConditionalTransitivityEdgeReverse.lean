import PASoundness.PAtoCompactConditionalTransitivityReverseExtract
import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.CompactFreshen

/-! Reverse coverage of an explicitly supplied restricted composition graph.
The two input bijections and the composition condition remain premises; no
graph construction, quotient transitivity, or semantic shortcut is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityEdgeReverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityReverseExtract
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def premises : Formula := namedBoth bijectionFormula (namedBoth secondBijection
  (namedBoth composition (.member 8 3)))
def midBody : Formula := namedBoth (.member 1 10) (graphFormula 7 10 3)
def sourceBody : Formula := namedBoth (.member 0 2) (graphFormula 6 2 10)
def outputBody : Formula := namedBoth (.member 0 2) (graphFormula 9 2 3)
def output : Formula := .ex 2 outputBody

private theorem premises_names_lt : ∀ v ∈ premises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ premises.names.sup id at hm
  have hb : premises.names.sup id < 30 := by decide
  omega
private def freshPremises := freshen premises 30 premises_names_lt
private theorem fresh_no2 : 2 ∉ freshPremises.formula.names := by decide
private theorem fresh_no10 : 10 ∉ freshPremises.formula.names := by decide
private def premisesVacuity (v : Nat) (h : v ∉ freshPremises.formula.names) :
    KDerivation (imp premises.encode (allCode v premises.encode)) :=
  compose freshPremises.equivalent.forward
    (compose (freshPremises.formula.vacuity v h)
      (allCongr v freshPremises.equivalent.backward))

private theorem output_names_lt : ∀ v ∈ output.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ output.names.sup id at hm
  have hb : output.names.sup id < 30 := by decide
  omega
private def freshOutput := freshen output 30 output_names_lt
private theorem output_no2 : 2 ∉ freshOutput.formula.names := by decide
private def outputVacuity2 : KDerivation (imp output.encode (allCode 2 output.encode)) :=
  compose freshOutput.equivalent.forward
    (compose (freshOutput.formula.vacuity 2 output_no2)
      (allCongr 2 freshOutput.equivalent.backward))

/-- For every specified target element, the supplied second and first
bijections give one shared path and hence an edge of the supplied composite. -/
def reverse_edge_exists : KDerivation (imp premises.encode output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h : Context Γ premises.encode := Context.head [] _
  have hf : Context Γ bijectionFormula.encode := Context.conjunctionLeft h
  have ht := Context.conjunctionRight h
  have hg : Context Γ secondBijection.encode := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have hc : Context Γ composition.encode := Context.conjunctionLeft ht
  have hz : Context Γ (member 8 3) := Context.conjunctionRight ht
  have hm : Context Γ (existsCode 10 midBody.encode) := by
    exact .mp hz (.mp hg (.closed g_preimage))
  have hs : Context (midBody.encode :: Γ) (existsCode 2 sourceBody.encode) := by
    have hm' : Context (midBody.encode :: Γ) midBody.encode := Context.head Γ _
    have hmid : Context (midBody.encode :: Γ) (member 1 10) := Context.conjunctionLeft hm'
    exact .mp hmid (.mp (Context.under hf _) (.closed f_preimage))
  have hlocal : Context (sourceBody.encode :: midBody.encode :: Γ) output.encode := by
    let Δ := sourceBody.encode :: midBody.encode :: Γ
    have hsrc : Context Δ sourceBody.encode := Context.head _ _
    have hmid : Context Δ midBody.encode := Context.under (Context.head Γ midBody.encode) sourceBody.encode
    have ha : Context Δ (member 0 2) := Context.conjunctionLeft hsrc
    have hfe : Context Δ (graphFormula 6 2 10).encode := Context.conjunctionRight hsrc
    have hb : Context Δ (member 1 10) := Context.conjunctionLeft hmid
    have hge : Context Δ (graphFormula 7 10 3).encode := Context.conjunctionRight hmid
    have hc' : Context Δ composition.encode := .under (.under hc _) _
    have hz' : Context Δ (member 8 3) := .under (.under hz _) _
    have he : Context Δ edge.encode :=
      .mp hge (.mp hfe (.mp hb (.mp hz' (.mp ha (.mp hc' (.closed chain_to_edge))))))
    have hout : Context Δ outputBody.encode := Context.conjunctionIntro ha he
    exact .mp hout (.closed (existsIntroduce 2 outputBody (by decide)))
  have hv2 : ∀ t, t ∈ midBody.encode :: Γ → KDerivation (imp t (allCode 2 t)) := by
    intro t ht
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at ht
    by_cases he : t = midBody.encode
    · subst t
      exact midBody.vacuity 2 (by decide)
    · have he' : t = premises.encode := ht.resolve_left he
      subst t
      exact premisesVacuity 2 fresh_no2
  have hmidOut : Context (midBody.encode :: Γ) output.encode :=
    Context.existsElim outputVacuity2
      (Context.generalize 2 hv2 (Context.deduction hlocal)) hs
  have hv10 : ∀ t, t ∈ Γ → KDerivation (imp t (allCode 10 t)) := by
    intro t ht
    have he : t = premises.encode := by simpa [Γ] using ht
    subst t
    exact premisesVacuity 10 fresh_no10
  exact Context.existsElim (output.vacuity 10 (by decide))
    (Context.generalize 10 hv10 (Context.deduction hmidOut)) hm

/-- Curried form for composing with the target bijection clause. -/
def reverse_edge_exists_curried : KDerivation (imp bijectionFormula.encode
    (imp secondBijection.encode (imp composition.encode (imp (member 8 3)
      (existsCode 2 (both (member 0 2) (graphFormula 9 2 3).encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 8 3, composition.encode, secondBijection.encode, bijectionFormula.encode]
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ composition.encode := .hypothesis (by simp [Γ])
  have hz : Context Γ (member 8 3) := Context.head _ _
  have hp : Context Γ premises.encode := Context.conjunctionIntro hf
    (Context.conjunctionIntro hg (Context.conjunctionIntro hc hz))
  exact .mp hp (.closed reverse_edge_exists)

theorem reverse_edge_exists_certificate : theoremCode (certificate reverse_edge_exists) =
    imp premises.encode output.encode := certificate_correct reverse_edge_exists

theorem reverse_edge_exists_curried_certificate : theoremCode (certificate reverse_edge_exists_curried) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp composition.encode
      (imp (member 8 3) (existsCode 2 (both (member 0 2) (graphFormula 9 2 3).encode))))) :=
  certificate_correct reverse_edge_exists_curried

end PASoundness.PAtoCompactConditionalTransitivityEdgeReverse

#print axioms PASoundness.PAtoCompactConditionalTransitivityEdgeReverse.reverse_edge_exists
#print axioms PASoundness.PAtoCompactConditionalTransitivityEdgeReverse.reverse_edge_exists_certificate
#print axioms PASoundness.PAtoCompactConditionalTransitivityEdgeReverse.reverse_edge_exists_curried

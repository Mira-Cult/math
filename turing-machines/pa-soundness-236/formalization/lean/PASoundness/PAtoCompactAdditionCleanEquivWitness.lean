import PASoundness.PAtoCompactCleanMatrix
import PASoundness.PAtoCompactCleanFilterExists
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactOrdinalAddition

/-! Build a clean old graph from an actual supplied old equivalence. The
cleaned graph is constructed by endpoint filtering in K. This gives no new
isomorphism extension, addition totality, or PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionCleanEquivWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanMatrix
open PASoundness.PAtoCompactCleanFilterExists PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactOrdinalAddition
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def body : Formula := namedBoth bijectionFormula orderFormula
private def cleanBody : Formula := namedBoth body
  (.all 19 (.imp (.member 6 19) (edgePredicate 19 0 1)))
private def cleanResult : Formula := .ex 6 cleanBody
private theorem clean_code : cleanBody.encode = both oldMatrix cleanGraph := by rfl
private theorem input_alpha : replace 6 10 body = oldMatrix10 := by rfl
private theorem source_shape : equivalentFormula = .ex 6 body := by rfl

private def from_filter : KDerivation
    (imp oldMatrix10.encode (imp filterCode cleanResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [filterCode,oldMatrix10.encode]
  have hf : Context Γ filterCode := .head _ _
  have ho : Context Γ oldMatrix10.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ cleanBody.encode := by
    rw [clean_code]
    exact .mp ho (.mp hf (.closed clean_matrix))
  exact .mp hc (.closed (existsIntroduce 6 cleanBody (by decide)))

private def from_original_graph : KDerivation (imp oldMatrix10.encode cleanResult.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [oldMatrix10.encode]
  have ho : Context Γ oldMatrix10.encode := .head _ _
  have hlocal : Context Γ (imp filterCode cleanResult.encode) := .mp ho (.closed from_filter)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    simp only [Γ,List.mem_singleton] at hh
    subst h
    exact oldMatrix10.vacuity 6 (by decide)
  have hall := Context.generalize 6 hv hlocal
  exact Context.existsElim (free_vacuity 6 cleanResult (by decide)) hall (.closed clean_filter_exists)

private def generic : KDerivation (imp equivalentFormula.encode cleanResult.encode) := by
  have ha := (existentialAlpha 6 10 body (by decide) (by decide) (by decide)).1
  rw [input_alpha] at ha
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [equivalentFormula.encode]
  have hs : Context Γ (existsCode 10 oldMatrix10.encode) := by
    have hh : Context Γ (existsCode 6 body.encode) := by
      have hh0 : Context Γ equivalentFormula.encode := .head _ _
      change Context Γ (existsCode 6 body.encode) at hh0
      exact hh0
    exact .mp hh (.closed ha)
  exact Context.existsElim (cleanResult.vacuity 10 (by decide))
    (.closed (.generalize 10 from_original_graph)) hs

private def moved := replace 0 31 (.imp equivalentFormula cleanResult)
private def moved_proved : KDerivation moved.encode := by
  have hi := universalInstance 0 31 (.imp equivalentFormula cleanResult) (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 generic) hi

/-- Old source 31 is equivalent to old suffix 34. K constructs some graph
at label 6 simultaneously satisfying the corresponding old isomorphism
matrix and endpoint cleanliness. -/
def clean_equiv_witness : KDerivation
    (imp (equivAt 31 34).encode (existsCode 6
      (namedBoth (namedBoth (replace 1 34 (replace 0 31 bijectionFormula))
        (replace 1 34 (replace 0 31 orderFormula)))
        (.all 19 (.imp (.member 6 19) (edgePredicate 19 31 34)))).encode)) := by
  have hi := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 1 moved_proved) hi
  have hs : replace 1 34 moved = .imp (equivAt 31 34)
      (.ex 6 (namedBoth (namedBoth (replace 1 34 (replace 0 31 bijectionFormula))
        (replace 1 34 (replace 0 31 orderFormula)))
        (.all 19 (.imp (.member 6 19) (edgePredicate 19 31 34))))) := by decide
  rw [hs] at h
  exact h

theorem clean_equiv_witness_certificate : theoremCode (certificate clean_equiv_witness) =
    imp (equivAt 31 34).encode (existsCode 6
      (namedBoth (namedBoth (replace 1 34 (replace 0 31 bijectionFormula))
        (replace 1 34 (replace 0 31 orderFormula)))
        (.all 19 (.imp (.member 6 19) (edgePredicate 19 31 34)))).encode) :=
  certificate_correct clean_equiv_witness
end PASoundness.PAtoCompactAdditionCleanEquivWitness
#print axioms PASoundness.PAtoCompactAdditionCleanEquivWitness.clean_equiv_witness
#print axioms PASoundness.PAtoCompactAdditionCleanEquivWitness.clean_equiv_witness_certificate

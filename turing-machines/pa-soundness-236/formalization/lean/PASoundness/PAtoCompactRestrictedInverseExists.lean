import PASoundness.PAtoCompactRestrictedInverseWitness
import PASoundness.PAtoCompactTransitiveWitness

/-! Existentially package the domain-restricted witness transfer. The two
restricted graph implications and target membership are explicit premises;
no inverse graph, global bijection or symmetry is constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedInverseWitness
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def forwardFormula : Formula := .all 2 (.imp (conj (.member 1 3) (.member 0 2))
  (.imp (graphFormula 6 2 3) (graphFormula 7 3 2)))

def backwardFormula : Formula := .all 4 (.imp (conj (.member 1 3) (.member 0 4))
  (.imp (graphFormula 7 3 4) (graphFormula 6 4 3)))

/-- Restricted correspondence carries an old existential preimage to a new
existential inverse-oriented image, retaining the target membership guard. -/
def guarded_inverse_exists : KDerivation
    (imp forwardFormula.encode (imp backwardFormula.encode (imp guardY
      (imp (existsCode 2 oldWitness) (existsCode 2 newWitness))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let F := forwardFormula.encode
  let B := backwardFormula.encode
  let Γ := [existsCode 2 oldWitness,guardY,B,F]
  have hw : Context Γ (existsCode 2 oldWitness) := Context.head _ _
  have hy : Context Γ guardY := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hya : Context Γ (allCode 2 guardY) :=
    .mp hy (.closed (membershipVacuity 1 3 2 (by decide) (by decide)))
  have hba : Context Γ (allCode 2 B) :=
    .mp hb (.closed (backwardFormula.vacuity 2 (by decide)))
  have hl : Context Γ (allCode 2 (imp guardY (imp forwardAt2
      (imp backwardAll (imp oldWitness newWitness))))) :=
    .closed (.generalize 2 guarded_inverse_witness)
  have hf' : Context Γ (allCode 2 forwardAt2) := hf
  have hb' : Context Γ (allCode 2 backwardAll) := hba
  have hall : Context Γ (allCode 2 (imp oldWitness newWitness)) :=
    Context.allMP hb' (Context.allMP hf' (Context.allMP hya hl))
  exact exists_map_context hall hw

theorem guarded_inverse_exists_certificate :
    theoremCode (certificate guarded_inverse_exists) =
      imp forwardFormula.encode (imp backwardFormula.encode (imp guardY
        (imp (existsCode 2 oldWitness) (existsCode 2 newWitness)))) :=
  certificate_correct guarded_inverse_exists

end PASoundness.PAtoCompactRestrictedInverseExists

#print axioms PASoundness.PAtoCompactRestrictedInverseExists.guarded_inverse_exists
#print axioms PASoundness.PAtoCompactRestrictedInverseExists.guarded_inverse_exists_certificate

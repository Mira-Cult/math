import PASoundness.PAtoCompactInverseWitness
import PASoundness.PAtoCompactTransitiveWitness

/-! Existential packaging for one supplied inverse-bijection witness. The
inverse graph is not constructed: both graph-implication families remain
explicit antecedents. This is not full bijection transfer or symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInverseExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactInverseWitness
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- All old edges into the fixed target are also reverse-oriented edges. -/
def forwardFormula : Formula := .all 2
  (.imp (graphFormula 6 2 3) (graphFormula 7 3 2))

/-- Reverse-oriented edges from the fixed target are old edges into it. -/
def reverseFormula : Formula := .all 4
  (.imp (graphFormula 7 3 4) (graphFormula 6 4 3))

/-- Under the two explicit graph-conversion families, an existential old
preimage witness gives an existential reverse-oriented witness with its
uniqueness condition. The input and output existential both bind name 2;
name 3 and both graph codes remain free, and 4 is the uniqueness binder. -/
def inverse_exists : KDerivation
    (imp forwardFormula.encode (imp reverseFormula.encode
      (imp (existsCode 2 oldWitness) (existsCode 2 newWitness)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let F := forwardFormula.encode
  let R := reverseFormula.encode
  let W := oldWitness
  let W' := newWitness
  let Γ := [existsCode 2 W,R,F]
  have hw : Context Γ (existsCode 2 W) := Context.head _ _
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hvR : KDerivation (imp R (allCode 2 R)) := by
    exact reverseFormula.vacuity 2 (by decide)
  have hRall : Context Γ (allCode 2 R) := .mp hr (.closed hvR)
  have hlocal : Context Γ (allCode 2
      (imp (imp oldGraph newGraph) (imp R (imp W W')))) :=
    .closed (.generalize 2 inverse_witness)
  have hF : Context Γ (allCode 2 (imp oldGraph newGraph)) := by
    exact hf
  have hall : Context Γ (allCode 2 (imp W W')) :=
    Context.allMP hRall (Context.allMP hF hlocal)
  exact exists_map_context hall hw

theorem inverse_exists_certificate : theoremCode (certificate inverse_exists) =
    imp forwardFormula.encode (imp reverseFormula.encode
      (imp (existsCode 2 oldWitness) (existsCode 2 newWitness))) :=
  certificate_correct inverse_exists

end PASoundness.PAtoCompactInverseExists

#print axioms PASoundness.PAtoCompactInverseExists.inverse_exists
#print axioms PASoundness.PAtoCompactInverseExists.inverse_exists_certificate

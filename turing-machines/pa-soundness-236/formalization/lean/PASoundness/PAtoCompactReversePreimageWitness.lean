import PASoundness.PAtoCompactInverseWitness

/-! Fixed-witness transfer of the original image clause to the inverse
preimage clause. Both graph-conversion implications remain explicit
antecedents; the inverse graph is not constructed. Code 1 is literal encoded
falsum. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReversePreimageWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldGraph : Nat := (graphFormula 6 2 3).encode
def newGraph : Nat := (graphFormula 7 3 2).encode
def oldAt4 : Nat := (graphFormula 6 2 4).encode
def newAt4 : Nat := (graphFormula 7 4 2).encode
def oldUnique : Nat := allCode 4 (imp (both (member 1 4) oldAt4) (equal 4 3))
def newUnique : Nat := allCode 4 (imp (both (member 1 4) newAt4) (equal 4 3))
def oldWitness : Nat := both (member 1 3) (both oldGraph oldUnique)
def newWitness : Nat := both (member 1 3) (both newGraph newUnique)

/-- A fixed image witness transfers to a preimage witness when the explicit
forward conversion holds at this witness and the reverse conversion holds at
each possible competing output. Labels 0,1,2,3,4,6,7 avoid the internal
pair-graph binders 19–22. -/
def inverse_witness : KDerivation
    (imp (imp oldGraph newGraph)
      (imp (allCode 4 (imp newAt4 oldAt4)) (imp oldWitness newWitness))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := imp oldGraph newGraph
  let R := allCode 4 (imp newAt4 oldAt4)
  let Γ := [oldWitness,R,C]
  have hw : Context Γ oldWitness := Context.head _ _
  have hx : Context Γ (member 1 3) := Context.conjunctionLeft hw
  have hw' : Context Γ (both oldGraph oldUnique) := Context.conjunctionRight hw
  have hg : Context Γ oldGraph := Context.conjunctionLeft hw'
  have hu : Context Γ oldUnique := Context.conjunctionRight hw'
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hn : Context Γ newGraph := .mp hg hc
  have hnu : Context Γ newUnique := by
    exact .mp hu (.mp hr (.closed
      (PASoundness.PAtoCompactInverseWitness.all_uniqueness_transport
        4 (member 1 4) oldAt4 newAt4 (equal 4 3))))
  exact Context.conjunctionIntro hx (Context.conjunctionIntro hn hnu)

theorem inverse_witness_certificate : theoremCode (certificate inverse_witness) =
    imp (imp oldGraph newGraph)
      (imp (allCode 4 (imp newAt4 oldAt4)) (imp oldWitness newWitness)) :=
  certificate_correct inverse_witness

end PASoundness.PAtoCompactReversePreimageWitness

#print axioms PASoundness.PAtoCompactReversePreimageWitness.inverse_witness
#print axioms PASoundness.PAtoCompactReversePreimageWitness.inverse_witness_certificate

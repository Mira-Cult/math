import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! A witness-transfer lemma for an inverse graph correspondence restricted
to the two candidate domains. It constructs no inverse graph and does not
modify the candidate equivalence formula. Code 1 remains literal K falsum. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guardY : Nat := member 1 3
def guardX : Nat := member 0 2
def guardX4 : Nat := member 0 4
def oldEdge : Nat := (graphFormula 6 2 3).encode
def newEdge : Nat := (graphFormula 7 3 2).encode
def oldEdge4 : Nat := (graphFormula 6 4 3).encode
def newEdge4 : Nat := (graphFormula 7 3 4).encode
def oldUnique : Nat := allCode 4 (imp (both guardX4 oldEdge4) (equal 4 2))
def newUnique : Nat := allCode 4 (imp (both guardX4 newEdge4) (equal 4 2))
def oldWitness : Nat := both guardX (both oldEdge oldUnique)
def newWitness : Nat := both guardX (both newEdge newUnique)
def forwardAt2 : Nat := imp (both guardY guardX) (imp oldEdge newEdge)
def backwardAt4 : Nat := imp (both guardY guardX4) (imp newEdge4 oldEdge4)
def backwardAll : Nat := allCode 4 backwardAt4

/-- Guarded uniqueness transport is a closed propositional K proof. -/
def guarded_uniqueness (Y X G H E : Nat) : KDerivation
    (imp Y (imp (imp (both Y X) (imp H G))
      (imp (imp (both X G) E) (imp (both X H) E)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [both X H,imp (both X G) E,imp (both Y X) (imp H G),Y]
  have hxh : Context Γ (both X H) := Context.head _ _
  have hx : Context Γ X := Context.conjunctionLeft hxh
  have hh : Context Γ H := Context.conjunctionRight hxh
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have hc : Context Γ (imp (both Y X) (imp H G)) := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .mp hh (.mp (Context.conjunctionIntro hy hx) hc)
  have hu : Context Γ (imp (both X G) E) := .hypothesis (by simp [Γ])
  exact .mp (Context.conjunctionIntro hx hg) hu

/-- The domain-restricted correspondence transfers a fixed old preimage
witness and its complete uniqueness condition. Every named guard and graph
conversion remains an explicit antecedent. -/
def guarded_inverse_witness : KDerivation
    (imp guardY (imp forwardAt2 (imp backwardAll (imp oldWitness newWitness)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldWitness,backwardAll,forwardAt2,guardY]
  have hw : Context Γ oldWitness := Context.head _ _
  have hy : Context Γ guardY := .hypothesis (by simp [Γ])
  have hf : Context Γ forwardAt2 := .hypothesis (by simp [Γ])
  have hb : Context Γ backwardAll := .hypothesis (by simp [Γ])
  have hx : Context Γ guardX := Context.conjunctionLeft hw
  have hw' : Context Γ (both oldEdge oldUnique) := Context.conjunctionRight hw
  have he : Context Γ oldEdge := Context.conjunctionLeft hw'
  have hu : Context Γ oldUnique := Context.conjunctionRight hw'
  have hn : Context Γ newEdge := .mp he (.mp (Context.conjunctionIntro hy hx) hf)
  have hyall : Context Γ (allCode 4 guardY) := by
    exact .mp hy (.closed (membershipVacuity 1 3 4 (by decide) (by decide)))
  have hlocal : Context Γ (allCode 4 (imp guardY (imp backwardAt4
      (imp (imp (both guardX4 oldEdge4) (equal 4 2))
        (imp (both guardX4 newEdge4) (equal 4 2)))))) :=
    .closed (.generalize 4 (guarded_uniqueness guardY guardX4 oldEdge4 newEdge4 (equal 4 2)))
  have hnew : Context Γ newUnique := Context.allMP hu
    (Context.allMP hb (Context.allMP hyall hlocal))
  exact Context.conjunctionIntro hx (Context.conjunctionIntro hn hnew)

theorem guarded_inverse_witness_certificate :
    theoremCode (certificate guarded_inverse_witness) =
      imp guardY (imp forwardAt2 (imp backwardAll (imp oldWitness newWitness))) :=
  certificate_correct guarded_inverse_witness

end PASoundness.PAtoCompactRestrictedInverseWitness

#print axioms PASoundness.PAtoCompactRestrictedInverseWitness.guarded_inverse_witness
#print axioms PASoundness.PAtoCompactRestrictedInverseWitness.guarded_inverse_witness_certificate

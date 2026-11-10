import PASoundness.PAtoCompactRestrictedInverseSecondWitness
import PASoundness.PAtoCompactTransitiveWitness

/-! Existential and quantified packaging for the complementary inverse
bijection clause under correspondence restricted to the two displayed
domains. No inverse graph or symmetry is constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseSecondExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactReversePreimageWitness
open PASoundness.PAtoCompactRestrictedInverseSecondWitness PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def forwardFormula : Formula := .all 3 (.imp (conj (.member 1 3) (.member 0 2))
  (.imp (graphFormula 6 2 3) (graphFormula 7 3 2)))

def backwardFormula : Formula := .all 4 (.imp (conj (.member 1 4) (.member 0 2))
  (.imp (graphFormula 7 4 2) (graphFormula 6 2 4)))

/-- The source guard and both restricted correspondence families transfer an
old existential image witness to a new existential preimage witness. -/
def guarded_inverse_exists : KDerivation
    (imp forwardFormula.encode (imp backwardFormula.encode (imp guardX
      (imp (existsCode 3 oldWitness) (existsCode 3 newWitness))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let F := forwardFormula.encode
  let B := backwardFormula.encode
  let Γ := [existsCode 3 oldWitness,guardX,B,F]
  have hw : Context Γ (existsCode 3 oldWitness) := Context.head _ _
  have hx : Context Γ guardX := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hxa : Context Γ (allCode 3 guardX) :=
    .mp hx (.closed (membershipVacuity 0 2 3 (by decide) (by decide)))
  have hba : Context Γ (allCode 3 B) :=
    .mp hb (.closed (backwardFormula.vacuity 3 (by decide)))
  have hl : Context Γ (allCode 3 (imp guardX (imp forwardAt3
      (imp backwardAll (imp oldWitness newWitness))))) :=
    .closed (.generalize 3 guarded_inverse_witness)
  have hf' : Context Γ (allCode 3 forwardAt3) := hf
  have hb' : Context Γ (allCode 3 backwardAll) := hba
  have hall : Context Γ (allCode 3 (imp oldWitness newWitness)) :=
    Context.allMP hb' (Context.allMP hf' (Context.allMP hxa hl))
  exact exists_map_context hall hw

theorem guarded_inverse_exists_certificate : theoremCode (certificate guarded_inverse_exists) =
    imp forwardFormula.encode (imp backwardFormula.encode (imp guardX
      (imp (existsCode 3 oldWitness) (existsCode 3 newWitness)))) :=
  certificate_correct guarded_inverse_exists

/-- Closed implication combinator used under a universal quantifier. -/
def guard_transfer (G F B A C : Nat) : KDerivation
    (imp (imp F (imp B (imp G (imp A C))))
      (imp F (imp B (imp (imp G A) (imp G C))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [G,imp G A,B,F,imp F (imp B (imp G (imp A C)))]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ha : Context Γ (imp G A) := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ht : Context Γ (imp F (imp B (imp G (imp A C)))) := .hypothesis (by simp [Γ])
  exact .mp (.mp hg ha) (.mp hg (.mp hb (.mp hf ht)))

def globalForward : Nat := allCode 2 forwardFormula.encode
def globalBackward : Nat := allCode 2 backwardFormula.encode
def oldImageClause : Nat := allCode 2 (imp guardX (existsCode 3 oldWitness))
def newPreimageClause : Nat := allCode 2 (imp guardX (existsCode 3 newWitness))

/-- Under displayed restricted correspondence, the complete old image
clause yields the complete reverse preimage clause. -/
def guarded_image_clause : KDerivation
    (imp globalForward (imp globalBackward (imp oldImageClause newPreimageClause))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldImageClause,globalBackward,globalForward]
  have hi : Context Γ oldImageClause := Context.head _ _
  have hb : Context Γ globalBackward := .hypothesis (by simp [Γ])
  have hf : Context Γ globalForward := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 2 (imp forwardFormula.encode
      (imp backwardFormula.encode (imp guardX (imp (existsCode 3 oldWitness)
        (existsCode 3 newWitness)))))) := .closed (.generalize 2 guarded_inverse_exists)
  have hg : Context Γ (allCode 2
      (imp (imp forwardFormula.encode (imp backwardFormula.encode
        (imp guardX (imp (existsCode 3 oldWitness) (existsCode 3 newWitness)))))
        (imp forwardFormula.encode (imp backwardFormula.encode
          (imp (imp guardX (existsCode 3 oldWitness)) (imp guardX (existsCode 3 newWitness))))))) :=
    .closed (.generalize 2 (guard_transfer guardX forwardFormula.encode backwardFormula.encode
      (existsCode 3 oldWitness) (existsCode 3 newWitness)))
  have hlocal : Context Γ (allCode 2 (imp (imp guardX (existsCode 3 oldWitness))
      (imp guardX (existsCode 3 newWitness)))) := Context.allMP hb (Context.allMP hf (Context.allMP hl hg))
  exact Context.allMP hi hlocal

theorem guarded_image_clause_certificate : theoremCode (certificate guarded_image_clause) =
    imp globalForward (imp globalBackward (imp oldImageClause newPreimageClause)) :=
  certificate_correct guarded_image_clause

end PASoundness.PAtoCompactRestrictedInverseSecondExists

#print axioms PASoundness.PAtoCompactRestrictedInverseSecondExists.guarded_inverse_exists
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondExists.guarded_image_clause
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondExists.guarded_image_clause_certificate

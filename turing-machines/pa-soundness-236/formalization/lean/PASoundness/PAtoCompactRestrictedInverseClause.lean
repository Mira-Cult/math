import PASoundness.PAtoCompactRestrictedInverseExists

/-! Complete one inverse-bijection clause under correspondence restricted to
the two displayed domains. No inverse graph, other clause, or symmetry is
constructed; all graph-correspondence conditions remain explicit premises. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseClause
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactRestrictedInverseWitness PASoundness.PAtoCompactRestrictedInverseExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Distribute one shared guard through an implication in literal K. -/
def guarded_apply (Y A B : Nat) : KDerivation
    (imp (imp Y (imp A B)) (imp (imp Y A) (imp Y B))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Y,imp Y A,imp Y (imp A B)]
  have hy : Context Γ Y := Context.head _ _
  have ha : Context Γ (imp Y A) := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp Y (imp A B)) := .hypothesis (by simp [Γ])
  exact .mp (.mp hy ha) (.mp hy hb)

def globalForward : Nat := allCode 3 forwardFormula.encode
def globalBackward : Nat := allCode 3 backwardFormula.encode
def oldPreimageClause : Nat := allCode 3 (imp guardY (existsCode 2 oldWitness))
def newImageClause : Nat := allCode 3 (imp guardY (existsCode 2 newWitness))

/-- Restricted global correspondence and the original preimage clause yield
the reverse-oriented image clause for all target-domain elements. -/
def guarded_preimage_clause : KDerivation
    (imp globalForward (imp globalBackward (imp oldPreimageClause newImageClause))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldPreimageClause,globalBackward,globalForward]
  have ho : Context Γ oldPreimageClause := Context.head _ _
  have hb : Context Γ globalBackward := .hypothesis (by simp [Γ])
  have hf : Context Γ globalForward := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 3 (imp forwardFormula.encode (imp backwardFormula.encode
      (imp guardY (imp (existsCode 2 oldWitness) (existsCode 2 newWitness)))))) :=
    .closed (.generalize 3 guarded_inverse_exists)
  have hm : Context Γ (allCode 3 (imp guardY
      (imp (existsCode 2 oldWitness) (existsCode 2 newWitness)))) :=
    Context.allMP hb (Context.allMP hf hl)
  have hd : Context Γ (allCode 3 (imp
      (imp guardY (imp (existsCode 2 oldWitness) (existsCode 2 newWitness)))
      (imp (imp guardY (existsCode 2 oldWitness))
        (imp guardY (existsCode 2 newWitness))))) :=
    .closed (.generalize 3 (guarded_apply guardY (existsCode 2 oldWitness)
      (existsCode 2 newWitness)))
  exact Context.allMP ho (Context.allMP hm hd)

theorem guarded_preimage_clause_certificate :
    theoremCode (certificate guarded_preimage_clause) =
      imp globalForward (imp globalBackward (imp oldPreimageClause newImageClause)) :=
  certificate_correct guarded_preimage_clause

end PASoundness.PAtoCompactRestrictedInverseClause

#print axioms PASoundness.PAtoCompactRestrictedInverseClause.guarded_preimage_clause
#print axioms PASoundness.PAtoCompactRestrictedInverseClause.guarded_preimage_clause_certificate

import PASoundness.PAtoCompactInverseExists

/-! One complete clause of inverse-bijection transport, conditional on two
explicit global graph-correspondence families. This constructs no inverse
graph and does not establish the other clause, order transport or symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInverseBijection
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactInverseWitness PASoundness.PAtoCompactInverseExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A generic propositional composition in the literal K proof calculus. -/
def guarded_compose (G A B : Nat) : KDerivation
    (imp (imp A B) (imp (imp G A) (imp G B))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [G,imp G A,imp A B]
  have hg : Context Γ G := Context.head _ _
  have ha : Context Γ (imp G A) := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp A B) := .hypothesis (by simp [Γ])
  exact .mp (.mp hg ha) hb

def globalForward : Nat := allCode 3 forwardFormula.encode
def globalReverse : Nat := allCode 3 reverseFormula.encode

def oldPreimageClause : Nat := allCode 3
  (imp (member 1 3) (existsCode 2 oldWitness))

def newImageClause : Nat := allCode 3
  (imp (member 1 3) (existsCode 2 newWitness))

/-- A supplied inverse correspondence and old preimage-bijection clause yield
the corresponding reverse image-bijection clause for every member of 1.
The correspondence families and old clause are explicit K antecedents;
none is proved or semantically assumed here. -/
def transfer_preimage_clause : KDerivation
    (imp globalForward (imp globalReverse (imp oldPreimageClause newImageClause))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldPreimageClause,globalReverse,globalForward]
  have hp : Context Γ oldPreimageClause := Context.head _ _
  have hr : Context Γ globalReverse := .hypothesis (by simp [Γ])
  have hf : Context Γ globalForward := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 3 (imp forwardFormula.encode (imp reverseFormula.encode
      (imp (existsCode 2 oldWitness) (existsCode 2 newWitness))))) :=
    .closed (.generalize 3 inverse_exists)
  have hab : Context Γ (allCode 3 (imp (existsCode 2 oldWitness) (existsCode 2 newWitness))) :=
    Context.allMP hr (Context.allMP hf hl)
  have hc : Context Γ (allCode 3 (imp (imp (existsCode 2 oldWitness) (existsCode 2 newWitness))
      (imp (imp (member 1 3) (existsCode 2 oldWitness))
        (imp (member 1 3) (existsCode 2 newWitness))))) :=
    .closed (.generalize 3 (guarded_compose (member 1 3)
      (existsCode 2 oldWitness) (existsCode 2 newWitness)))
  exact Context.allMP hp (Context.allMP hab hc)

theorem transfer_preimage_clause_certificate :
    theoremCode (certificate transfer_preimage_clause) =
      imp globalForward (imp globalReverse (imp oldPreimageClause newImageClause)) :=
  certificate_correct transfer_preimage_clause

end PASoundness.PAtoCompactInverseBijection

#print axioms PASoundness.PAtoCompactInverseBijection.transfer_preimage_clause
#print axioms PASoundness.PAtoCompactInverseBijection.transfer_preimage_clause_certificate

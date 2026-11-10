import PASoundness.PAtoCompactProductMatchPointWitness

/-! Uniqueness of both halves of a product-edge match. These are literal K
derivations from the uniqueness clauses retained with selected product
witnesses. They do not yet match different factor isomorphism graphs or
collect a graph of matches. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPointUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseUnique : Formula := .imp
  (namedBoth (.member 0 7) (namedBoth (.member 1 8) (tripleFormula 7 8 32)))
  (namedBoth (.equal 7 30) (.equal 8 31))

def reverseCompetitor : Formula :=
  namedBoth (.member 0 33) (namedBoth (.member 1 34) (tripleFormula 33 34 32))

theorem reverse_selected_shape : selectedReverseBody =
    namedBoth (.member 0 30) (namedBoth (.member 1 31)
      (namedBoth (tripleFormula 30 31 32) (.all 7 (.all 8 reverseUnique)))) := by decide

/-- Two coordinate pairs for the same output of one supplied product graph
have equal major and minor coordinates. -/
def reverse_coordinates_unique : KDerivation
    (imp selectedReverseBody.encode (imp reverseCompetitor.encode
      (both (equal 33 30) (equal 34 31)))) := by
  have h7 := universalInstance 7 33 (.all 8 reverseUnique)
    (by decide) (by decide) (by decide)
  have hs7 : replace 7 33 (.all 8 reverseUnique) =
      .all 8 (replace 7 33 reverseUnique) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 34 (replace 7 33 reverseUnique)
    (by decide) (by decide) (by decide)
  have hs8 : replace 8 34 (replace 7 33 reverseUnique) =
      .imp reverseCompetitor (namedBoth (.equal 33 30) (.equal 34 31)) := by decide
  rw [hs8] at h8
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [reverseCompetitor.encode, selectedReverseBody.encode]
  have hc : Context Γ reverseCompetitor.encode := .head _ _
  have hs : Context Γ selectedReverseBody.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both (member 0 30) (both (member 1 31)
      (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
    simpa [reverse_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hs
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hs'))
  have hp := Context.mp (Context.mp hu (.closed h7)) (.closed h8)
  have he := Context.mp hc hp
  simpa [namedBoth, Formula.not, Formula.encode, both, neg] using he

def forwardUnique : Formula := .imp
  (namedBoth (.member 2 9) (tripleFormula 30 31 9)) (.equal 9 32)

def forwardCompetitor : Formula :=
  namedBoth (.member 2 35) (tripleFormula 30 31 35)

theorem forward_selected_shape : selectedForwardBody =
    namedBoth (.member 2 32)
      (namedBoth (tripleFormula 30 31 32) (.all 9 forwardUnique)) := by decide

/-- Two outputs for the same coordinate pair in one supplied product graph
are equal. This establishes a pointwise uniqueness clause only. -/
def forward_output_unique : KDerivation
    (imp selectedForwardBody.encode (imp forwardCompetitor.encode (equal 35 32))) := by
  have h9 := universalInstance 9 35 forwardUnique (by decide) (by decide) (by decide)
  have hs9 : replace 9 35 forwardUnique = .imp forwardCompetitor (.equal 35 32) := by decide
  rw [hs9] at h9
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [forwardCompetitor.encode, selectedForwardBody.encode]
  have hc : Context Γ forwardCompetitor.encode := .head _ _
  have hs : Context Γ selectedForwardBody.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both (member 2 32)
      (both (tripleFormula 30 31 32).encode (allCode 9 forwardUnique.encode))) := by
    simpa [forward_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hs
  have hu := Context.conjunctionRight (Context.conjunctionRight hs')
  have hp := Context.mp hu (.closed h9)
  simpa [Formula.encode] using Context.mp hc hp

theorem reverse_coordinates_unique_certificate :
    theoremCode (certificate reverse_coordinates_unique) =
      imp selectedReverseBody.encode (imp reverseCompetitor.encode
        (both (equal 33 30) (equal 34 31))) := certificate_correct _

theorem forward_output_unique_certificate :
    theoremCode (certificate forward_output_unique) =
      imp selectedForwardBody.encode (imp forwardCompetitor.encode (equal 35 32)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchPointUnique

#print axioms PASoundness.PAtoCompactProductMatchPointUnique.reverse_coordinates_unique
#print axioms PASoundness.PAtoCompactProductMatchPointUnique.forward_output_unique
#print axioms PASoundness.PAtoCompactProductMatchPointUnique.reverse_coordinates_unique_certificate
#print axioms PASoundness.PAtoCompactProductMatchPointUnique.forward_output_unique_certificate

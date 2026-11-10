import PASoundness.PAtoCompactRestrictedForwardGuard
import PASoundness.PAtoCompactBijectionForwardAtSeven

/-! The supplied old forward witness's target uniqueness transfers to the
supplied restricted graph without changing the chosen output. Literal K
negation is implication to code 1 (`member 0 0`). -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactBijectionForwardAtSeven PASoundness.PAtoCompactRestrictedForwardPoint
open PASoundness.PAtoCompactRestrictedForwardGuard
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Restricted uniqueness for input 7 and the same displayed output 3. -/
def restrictedUnique : Formula := .all 4
  (.imp (namedBoth (.member 5 4) (graphFormula 8 7 4)) (.equal 4 3))

/-- Full restricted forward witness, retaining the same selected output 3. -/
def restrictedWitness : Formula := namedBoth (.member 5 3)
  (namedBoth (graphFormula 8 7 3) restrictedUnique)

/-- Given raw S(5,1), the endpoint filter, the full original witness at
input 7/output 3, and the same output's restricted membership and edge, K
derives the full restricted witness. Fixed labels are syntactic and do not
imply object inequality. This does not construct either witness or assert
universal coverage or an isomorphism. -/
def restricted_witness_from_original : KDerivation
    (imp (successorCode 5 1 10) (imp filter
      (imp witnessAtSeven.encode
        (imp (both (member 5 3) (graphFormula 8 7 3).encode)
          restrictedWitness.encode)))) := by
  let S := successorCode 5 1 10
  let F := filter
  let W := witnessAtSeven.encode
  let R := both (member 5 3) (graphFormula 8 7 3).encode
  let A := both (member 5 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let C := equal 4 3
  have hcomp : KDerivation (imp (imp A B) (imp (imp B C) (imp A C))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp B C,imp A B]
    have ha : Context Γ A := .head _ _
    have hab : Context Γ (imp A B) := .hypothesis (by simp [Γ])
    have hbc : Context Γ (imp B C) := .hypothesis (by simp [Γ])
    exact .mp (.mp ha hab) hbc
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [R,W,F,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .head _ _
  have hg : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hs (.closed restricted_guard_to_original))
  have hu : Context Γ (allCode 4 (imp B C)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have htransport : Context Γ (allCode 4 (imp (imp B C) (imp A C))) :=
    Context.allMP hg (.closed (.generalize 4 hcomp))
  have hnew : Context Γ (allCode 4 (imp A C)) := Context.allMP hu htransport
  have hm : Context Γ (member 5 3) := Context.conjunctionLeft hr
  have he : Context Γ (graphFormula 8 7 3).encode := Context.conjunctionRight hr
  exact Context.conjunctionIntro hm (Context.conjunctionIntro he hnew)

theorem restricted_witness_from_original_certificate :
    theoremCode (certificate restricted_witness_from_original) =
      imp (successorCode 5 1 10) (imp filter
        (imp witnessAtSeven.encode
          (imp (both (member 5 3) (graphFormula 8 7 3).encode)
            restrictedWitness.encode))) :=
  certificate_correct restricted_witness_from_original

end PASoundness.PAtoCompactRestrictedForwardUnique

#print axioms PASoundness.PAtoCompactRestrictedForwardUnique.restricted_witness_from_original
#print axioms PASoundness.PAtoCompactRestrictedForwardUnique.restricted_witness_from_original_certificate

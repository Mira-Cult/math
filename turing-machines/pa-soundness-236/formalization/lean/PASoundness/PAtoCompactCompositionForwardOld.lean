import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.CompactDerivations
import PASoundness.PAtoCompactCompositionAdjoinEdges

/-! Pointwise old-prefix forward coverage for a partially constructed
composition graph. Old invariant and edge-preservation proof are explicit;
this does not establish graph existence or the full successor invariant. -/
namespace PASoundness.PAtoCompactCompositionForwardOld
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The queried compositional path, with a shared middle witness. -/
def pathCode : Nat := existsCode 4 (both (member 1 4)
  (both (graphFormula 6 2 4).encode (graphFormula 7 4 3).encode))

/-- If the point-adjunction preserves old graph edges, a supplied old local
coverage implication carries an old-prefix path into the new graph. -/
def forward_old (preserve : KDerivation (imp (adjoinCode 9 16 17 18)
    (imp (graphFormula 9 2 3).encode (graphFormula 17 2 3).encode))) :
    KDerivation (imp (adjoinCode 9 16 17 18)
      (imp (imp (both (member 10 2) pathCode) (graphFormula 9 2 3).encode)
        (imp (member 10 2) (imp pathCode (graphFormula 17 2 3).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := adjoinCode 9 16 17 18
  let C := imp (both (member 10 2) pathCode) (graphFormula 9 2 3).encode
  let Γ := [pathCode,member 10 2,C,A]
  have hp : Context Γ pathCode := Context.head _ _
  have hm : Context Γ (member 10 2) := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hold : Context Γ (graphFormula 9 2 3).encode :=
    .mp (Context.conjunctionIntro hm hp) hc
  exact .mp hold (.mp ha (.closed preserve))

theorem forward_old_certificate (preserve : KDerivation (imp (adjoinCode 9 16 17 18)
    (imp (graphFormula 9 2 3).encode (graphFormula 17 2 3).encode))) :
    theoremCode (certificate (forward_old preserve)) =
      imp (adjoinCode 9 16 17 18)
        (imp (imp (both (member 10 2) pathCode) (graphFormula 9 2 3).encode)
          (imp (member 10 2) (imp pathCode (graphFormula 17 2 3).encode))) :=
  certificate_correct (forward_old preserve)

/-- The concrete adjunction proof discharges the edge-preservation input. -/
def forward_old_closed : KDerivation (imp (adjoinCode 9 16 17 18)
    (imp (imp (both (member 10 2) pathCode) (graphFormula 9 2 3).encode)
      (imp (member 10 2) (imp pathCode (graphFormula 17 2 3).encode)))) :=
  forward_old PASoundness.PAtoCompactCompositionAdjoinEdges.adjoin_preserves_edge

theorem forward_old_closed_certificate : theoremCode (certificate forward_old_closed) =
    imp (adjoinCode 9 16 17 18)
      (imp (imp (both (member 10 2) pathCode) (graphFormula 9 2 3).encode)
        (imp (member 10 2) (imp pathCode (graphFormula 17 2 3).encode))) :=
  certificate_correct forward_old_closed

end PASoundness.PAtoCompactCompositionForwardOld

#print axioms PASoundness.PAtoCompactCompositionForwardOld.forward_old
#print axioms PASoundness.PAtoCompactCompositionForwardOld.forward_old_certificate
#print axioms PASoundness.PAtoCompactCompositionForwardOld.forward_old_closed
#print axioms PASoundness.PAtoCompactCompositionForwardOld.forward_old_closed_certificate

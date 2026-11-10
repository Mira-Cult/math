import PASoundness.PAtoCompactPointAdjoin

/-! A fixed-name forward instance of a supplied point-adjunction graph.
This provides the case split needed for no-spurious-edge analysis; it does
not construct a graph or assert a pair uniqueness property. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseAdjoinInspect
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied graph h′=h∪{p} sends every inspected entry to the old graph
or the adjoined point. Fixed names: h=7, h′=9, p=11, test binder 14 and
entry 19. The disjunction is reordered to match the edge case split. -/
def adjoin_forward_instance : KDerivation
    (imp (adjoinCode 7 11 9 14)
      (imp (member 9 19) (either (member 7 19) (equal 19 11)))) := by
  let E := either (equal 19 11) (member 7 19)
  let B := both (imp (member 9 19) E) (imp E (member 9 19))
  let f : Formula := namedBoth (.imp (.member 9 14)
      (namedEither (.equal 14 11) (.member 7 14)))
    (.imp (namedEither (.equal 14 11) (.member 7 14)) (.member 9 14))
  have hi := universalInstance 14 19 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (adjoinCode 7 11 9 14) B) := by
    simpa [f, adjoinCode, B, E, namedBoth, namedEither, Formula.encode,
      CompactNamed.replace, CompactNamed.rename, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 9 19,adjoinCode 7 11 9 14]
  have ha : Context Γ (adjoinCode 7 11 9 14) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 19) := Context.head _ _
  have hb : Context Γ B := .mp ha (.closed hi')
  have he : Context Γ E := .mp hm (Context.conjunctionLeft hb)
  apply Context.disjunctionElim he
  · exact Context.disjunctionRight (a := member 7 19) (Context.head _ _)
  · exact Context.disjunctionLeft (b := equal 19 11) (Context.head _ _)

theorem adjoin_forward_instance_certificate :
    theoremCode (certificate adjoin_forward_instance) =
      imp (adjoinCode 7 11 9 14)
        (imp (member 9 19) (either (member 7 19) (equal 19 11))) :=
  certificate_correct adjoin_forward_instance

end PASoundness.PAtoCompactPartialInverseAdjoinInspect

#print axioms PASoundness.PAtoCompactPartialInverseAdjoinInspect.adjoin_forward_instance
#print axioms PASoundness.PAtoCompactPartialInverseAdjoinInspect.adjoin_forward_instance_certificate

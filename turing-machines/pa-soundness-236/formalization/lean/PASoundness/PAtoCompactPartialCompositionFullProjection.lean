import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.PAtoCompactPartialCompositionPathAlpha

/-! Project a supplied partial-composition graph at its full source prefix
to the exact restricted-composition condition. This constructs no graph and
does not prove quotient transitivity. Code 1 remains literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionFullProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPartialCompositionBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The invariant evaluated at its full source prefix. -/
def fullPrefix : Formula := replace 10 0 partialComposition

def pointFull : Formula := match fullPrefix with
  | .all _ (.all _ f) => f
  | _ => .truth

def pathFour : Formula := PAtoCompactPartialCompositionPathAlpha.pathFour

def pointFour : Formula := .imp
  (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) pathFour)
    (.imp pathFour (graphFormula 9 2 3)))

/-- With the prefix equal to the source, the source-domain guard supplies
prefix membership; both edge/path directions remain explicit K derivations. -/
def point_projection : KDerivation (imp pointFull.encode pointFour.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let X := member 0 2
  let Y := member 8 3
  let E := (graphFormula 9 2 3).encode
  let P := pathFour.encode
  let B := both (imp E (both X P)) (imp (both X P) E)
  let F := imp (both X Y) B
  let Γ := [both X Y,F]
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hxy : Context Γ (both X Y) := Context.head _ _
  have hx : Context Γ X := Context.conjunctionLeft hxy
  have hb : Context Γ B := .mp hxy hf
  have hforward : Context Γ (imp E P) := by
    apply Context.deduction
    have he : Context (E :: Γ) E := Context.head _ _
    have ht : Context (E :: Γ) (both X P) :=
      .mp he (Context.under (Context.conjunctionLeft hb) E)
    exact Context.conjunctionRight ht
  have hback : Context Γ (imp P E) := by
    apply Context.deduction
    have hp : Context (P :: Γ) P := Context.head _ _
    have hx' : Context (P :: Γ) X := Context.under hx P
    exact .mp (Context.conjunctionIntro hx' hp)
      (Context.under (Context.conjunctionRight hb) P)
  exact Context.conjunctionIntro hforward hback

/-- The pointwise projection lifts through both source/target quantifiers. -/
def full_to_four : KDerivation (imp fullPrefix.encode
    (Formula.all 2 (Formula.all 3 pointFour)).encode) :=
  allCongr 2 (allCongr 3 point_projection)

/-- Rename the middle-path existential 4→10 while retaining the endpoint
guard and both directions of the graph/path relation. -/
def point_to_composition : KDerivation (imp pointFour.encode
    PAtoCompactConditionalTransitivityPoint.point.encode) := by
  let E := (graphFormula 9 2 3).encode
  let P := pathFour.encode
  let Q := PAtoCompactConditionalTransitivityPoint.path.encode
  let X := member 0 2
  let Y := member 8 3
  let B := both (imp E P) (imp P E)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [both X Y,imp (both X Y) B]
  have hpoint : Context Γ (imp (both X Y) B) := .hypothesis (by simp [Γ])
  have hxy : Context Γ (both X Y) := Context.head _ _
  have hb : Context Γ B := .mp hxy hpoint
  have hforward : Context Γ (imp E Q) := by
    apply Context.deduction
    have he : Context (E :: Γ) E := Context.head _ _
    have hp : Context (E :: Γ) P := .mp he (Context.under (Context.conjunctionLeft hb) E)
    exact .mp hp (.closed PAtoCompactPartialCompositionPathAlpha.path_to_target)
  have hback : Context Γ (imp Q E) := by
    apply Context.deduction
    have hq : Context (Q :: Γ) Q := Context.head _ _
    have hp : Context (Q :: Γ) P := .mp hq (.closed PAtoCompactPartialCompositionPathAlpha.path_from_target)
    exact .mp hp (Context.under (Context.conjunctionRight hb) Q)
  exact Context.conjunctionIntro hforward hback

/-- The same represented graph satisfies the exact composition formula. -/
def full_prefix_to_composition : KDerivation (imp fullPrefix.encode
    PAtoCompactConditionalTransitivityPoint.composition.encode) :=
  compose full_to_four (allCongr 2 (allCongr 3 point_to_composition))

theorem full_prefix_to_composition_certificate :
    theoremCode (certificate full_prefix_to_composition) =
      imp fullPrefix.encode PAtoCompactConditionalTransitivityPoint.composition.encode :=
  certificate_correct full_prefix_to_composition

/-- Project the same existential graph witness, without uniform selection. -/
def full_prefix_exists_to_composition_exists : KDerivation
    (imp (existsCode 9 fullPrefix.encode)
      (existsCode 9 PAtoCompactConditionalTransitivityPoint.composition.encode)) :=
  existsCongr 9 full_prefix_to_composition

theorem full_prefix_exists_to_composition_exists_certificate :
    theoremCode (certificate full_prefix_exists_to_composition_exists) =
      imp (existsCode 9 fullPrefix.encode)
        (existsCode 9 PAtoCompactConditionalTransitivityPoint.composition.encode) :=
  certificate_correct full_prefix_exists_to_composition_exists

end PASoundness.PAtoCompactPartialCompositionFullProjection

#print axioms PASoundness.PAtoCompactPartialCompositionFullProjection.full_to_four
#print axioms PASoundness.PAtoCompactPartialCompositionFullProjection.full_prefix_to_composition
#print axioms PASoundness.PAtoCompactPartialCompositionFullProjection.full_prefix_exists_to_composition_exists

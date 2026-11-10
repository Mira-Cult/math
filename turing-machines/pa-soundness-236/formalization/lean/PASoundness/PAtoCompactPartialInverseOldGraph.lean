import PASoundness.PAtoCompactPartialInversePointCase
import PASoundness.CompactQuantifiers

/-! Promote the old-pair branch of the pointwise adjunction split into the
exact existential graph predicate. This retains the explicit pair-alias proof
data premise and does not eliminate the new graph's witness or construct an
inverse graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOldGraph
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInversePointCase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Matrix of the exact old graph predicate after binding the pair witness. -/
def oldGraphBody : Formula := match graphFormula 7 3 2 with
  | .ex _ f => f
  | _ => .truth

/-- The displayed existing pair witness yields the exact old graph relation. -/
def old_graph_intro : KDerivation
    (imp (both (member 7 19) (pairFormula 19 3 2).encode) (graphFormula 7 3 2).encode) := by
  have hi := existsIntroduce 19 oldGraphBody (by decide)
  exact hi

/-- Replace only the existing-pair branch of a disjunction by old graph
existence; the coordinate-equality branch is retained verbatim. -/
def old_branch_promote : KDerivation
    (imp (either (both (member 7 19) (pairFormula 19 3 2).encode)
      (both (equal 3 13) (equal 2 12)))
      (either (graphFormula 7 3 2).encode (both (equal 3 13) (equal 2 12)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let L := both (member 7 19) (pairFormula 19 3 2).encode
  let R := both (equal 3 13) (equal 2 12)
  let G := (graphFormula 7 3 2).encode
  let Γ := [either L R]
  have hc : Context Γ (either L R) := Context.head [] _
  apply Context.disjunctionElim hc
  · have hl : Context (L :: Γ) L := Context.head _ _
    have hg : Context (L :: Γ) G := .mp hl (.closed old_graph_intro)
    exact Context.disjunctionLeft (b := R) hg
  · exact Context.disjunctionRight (a := G) (Context.head Γ R)

/-- An element of the adjoined graph yields an old graph edge or has the
appended coordinates, conditional on the explicit alias derivation. -/
def no_spurious_old_graph (hAlias : KDerivation pairAliasCode) : KDerivation
    (imp (imp (member 9 19) (either (member 7 19) (equal 19 11)))
      (imp (member 9 19) (imp (pairFormula 19 3 2).encode
        (imp (pairFormula 11 13 12).encode
          (either (graphFormula 7 3 2).encode (both (equal 3 13) (equal 2 12))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := imp (member 9 19) (either (member 7 19) (equal 19 11))
  let P := (pairFormula 19 3 2).encode
  let Q := (pairFormula 11 13 12).encode
  let Γ := [Q,P,member 9 19,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := Context.head _ _
  have hm : Context Γ (member 9 19) := .hypothesis (by simp [Γ])
  have hs : Context Γ (either (both (member 7 19) P) (both (equal 3 13) (equal 2 12))) :=
    .mp hq (.mp hp (.mp hm (.mp ha (.closed (no_spurious_point hAlias)))))
  exact .mp hs (.closed old_branch_promote)

theorem no_spurious_old_graph_certificate (hAlias : KDerivation pairAliasCode) :
    theoremCode (certificate (no_spurious_old_graph hAlias)) =
      imp (imp (member 9 19) (either (member 7 19) (equal 19 11)))
        (imp (member 9 19) (imp (pairFormula 19 3 2).encode
          (imp (pairFormula 11 13 12).encode
            (either (graphFormula 7 3 2).encode (both (equal 3 13) (equal 2 12)))))) :=
  certificate_correct (no_spurious_old_graph hAlias)

end PASoundness.PAtoCompactPartialInverseOldGraph

#print axioms PASoundness.PAtoCompactPartialInverseOldGraph.no_spurious_old_graph
#print axioms PASoundness.PAtoCompactPartialInverseOldGraph.no_spurious_old_graph_certificate

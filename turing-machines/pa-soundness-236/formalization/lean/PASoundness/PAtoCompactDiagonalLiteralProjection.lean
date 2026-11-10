import PASoundness.PAtoCompactPointAdjoin

/-! Projections from the exact fixed-name K successor and point-adjunction
hypotheses needed for diagonal coverage. These are finite syntactic derivations;
no witness existence, induction, graph collection or semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalLiteralProjection
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A successor graph classifies each of its members as the input itself or
an old member. -/
def successor_cases : KDerivation
    (imp (successorCode 0 1 2)
      (allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2))))) := by
  let A := imp (member 1 2) (either (equal 2 0) (member 0 2))
  let B := imp (either (equal 2 0) (member 0 2)) (member 1 2)
  have hlocal : KDerivation (imp (both A B) A) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionLeft (Context.head [] (both A B))
  exact allCongr 2 hlocal

/-- A point-adjoined graph includes each member of the old graph. -/
def adjoin_inclusion : KDerivation
    (imp (adjoinCode 6 8 7 19) (allCode 19 (imp (member 6 19) (member 7 19)))) := by
  let M := member 6 19
  let N := member 7 19
  let E := equal 19 8
  let P := either E M
  let A := imp N P
  let B := imp P N
  have hlocal : KDerivation (imp (both A B) (imp M N)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M,both A B]
    have hm : Context Γ M := Context.head _ _
    have hb : Context Γ (both A B) := .hypothesis (by simp [Γ])
    have hp : Context Γ P := Context.disjunctionRight (a := E) hm
    exact .mp hp (Context.conjunctionRight hb)
  exact allCongr 19 hlocal

/-- The supplied point belongs to the adjoined graph. -/
def adjoin_contains_point : KDerivation (imp (adjoinCode 6 8 7 19) (member 7 8)) := by
  let f : CompactNamed.Formula := namedBoth
    (.imp (.member 7 19) (namedEither (.equal 19 8) (.member 6 19)))
    (.imp (namedEither (.equal 19 8) (.member 6 19)) (.member 7 19))
  have hi := CompactNamed.universalInstance 19 8 f (by decide)
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.binders])
  have hi' : KDerivation (imp (adjoinCode 6 8 7 19)
      (both (imp (member 7 8) (either (equal 8 8) (member 6 8)))
        (imp (either (equal 8 8) (member 6 8)) (member 7 8)))) := by
    simpa [f, adjoinCode, namedBoth, namedEither, CompactNamed.Formula.encode,
      CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [adjoinCode 6 8 7 19]
  have ha : Context Γ (adjoinCode 6 8 7 19) := Context.head [] _
  have hp : Context Γ (both (imp (member 7 8) (either (equal 8 8) (member 6 8)))
      (imp (either (equal 8 8) (member 6 8)) (member 7 8))) := .mp ha (.closed hi')
  have he : Context Γ (equal 8 8) := .closed (equalityReflexive 8)
  exact .mp (Context.disjunctionLeft (b := member 6 8) he) (Context.conjunctionRight hp)

theorem coverage_projections_certificate :
    theoremCode (certificate successor_cases) =
      imp (successorCode 0 1 2)
        (allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2)))) ∧
    theoremCode (certificate adjoin_inclusion) =
      imp (adjoinCode 6 8 7 19) (allCode 19 (imp (member 6 19) (member 7 19))) ∧
    theoremCode (certificate adjoin_contains_point) =
      imp (adjoinCode 6 8 7 19) (member 7 8) :=
  ⟨certificate_correct successor_cases, certificate_correct adjoin_inclusion,
    certificate_correct adjoin_contains_point⟩

end PASoundness.PAtoCompactDiagonalLiteralProjection

#print axioms PASoundness.PAtoCompactDiagonalLiteralProjection.successor_cases
#print axioms PASoundness.PAtoCompactDiagonalLiteralProjection.adjoin_inclusion
#print axioms PASoundness.PAtoCompactDiagonalLiteralProjection.adjoin_contains_point
#print axioms PASoundness.PAtoCompactDiagonalLiteralProjection.coverage_projections_certificate

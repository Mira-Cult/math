import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveClosure

/-! Fixed-name K consequences of the supplied successor and point-adjunction
graphs used by the diagonal no-garbage step. These are conditional finite
syntactic derivations, not existence or induction claims. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalGraphPremises
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied successor graph contains its input. -/
def successor_endpoint : KDerivation (imp (successorCode 0 1 4) (member 1 0)) :=
  successor_contains_input 0 1 4 (by decide) (by decide)

/-- The supplied successor graph includes every member of the input. -/
def successor_inclusion : KDerivation
    (imp (successorCode 0 1 4) (allCode 3 (imp (member 0 3) (member 1 3)))) := by
  let S := successorCode 0 1 4
  have hlocal : KDerivation (imp S (imp (member 0 3) (member 1 3))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 0 3,S]
    have hm : Context Γ (member 0 3) := Context.head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hd : Context Γ (either (equal 3 0) (member 0 3)) :=
      Context.disjunctionRight (a := equal 3 0) hm
    exact .mp hd (.mp hs (.closed (successor_include 0 1 4 3 (by decide) (by decide) (by decide))))
  have hv : KDerivation (imp S (allCode 3 S)) :=
    successor_vacuity 0 1 4 3 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [S] S := Context.head [] S
  have hp : Context [S] (imp (member 0 3) (member 1 3)) := .mp hs (.closed hlocal)
  exact Context.generalize 3 (by
    intro h hh
    have he : h = S := by simpa using hh
    subst h
    exact hv) hp

/-- Any entry of the adjoined graph is its added point or an old entry. -/
def adjoin_entry : KDerivation (imp (adjoinCode 6 8 7 10)
    (imp (member 7 9) (either (equal 9 8) (member 6 9)))) := by
  let f : CompactNamed.Formula := namedBoth
    (.imp (.member 7 10) (namedEither (.equal 10 8) (.member 6 10)))
    (.imp (namedEither (.equal 10 8) (.member 6 10)) (.member 7 10))
  have hi := CompactNamed.universalInstance 10 9 f (by decide)
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.binders])
  have hi' : KDerivation (imp (adjoinCode 6 8 7 10)
      (both (imp (member 7 9) (either (equal 9 8) (member 6 9)))
        (imp (either (equal 9 8) (member 6 9)) (member 7 9)))) := by
    simpa [f, adjoinCode, namedBoth, namedEither, CompactNamed.Formula.encode,
      CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (.mp (Context.head [] (adjoinCode 6 8 7 10)) (.closed hi'))

theorem graph_premises_certificate :
    theoremCode (certificate successor_endpoint) = imp (successorCode 0 1 4) (member 1 0) ∧
    theoremCode (certificate successor_inclusion) =
      imp (successorCode 0 1 4) (allCode 3 (imp (member 0 3) (member 1 3))) ∧
    theoremCode (certificate adjoin_entry) =
      imp (adjoinCode 6 8 7 10) (imp (member 7 9) (either (equal 9 8) (member 6 9))) :=
  ⟨certificate_correct successor_endpoint, certificate_correct successor_inclusion,
    certificate_correct adjoin_entry⟩

end PASoundness.PAtoCompactDiagonalGraphPremises

#print axioms PASoundness.PAtoCompactDiagonalGraphPremises.successor_endpoint
#print axioms PASoundness.PAtoCompactDiagonalGraphPremises.successor_inclusion
#print axioms PASoundness.PAtoCompactDiagonalGraphPremises.adjoin_entry
#print axioms PASoundness.PAtoCompactDiagonalGraphPremises.graph_premises_certificate

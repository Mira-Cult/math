import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactPointAdjoinSelector
import PASoundness.PAtoCompactGraphAdjoinPreserve
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactAdjunction

/-! One explicit K graph extension for the multiplication graph shape. Given
coordinate labels 30,31 and value label 32, K constructs their nested pair,
adjoins it to graph 6, and obtains the new triple edge. This is one point,
not collection of an entire row, product-graph existence, or multiplication
totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiAnyNames
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactPointAdjoinSelector
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The exact product-style triple relation, with its graph label explicit. -/
def tripleAt (g a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula g 18 c))

/-- The first witness is the ordered pair of source coordinates. -/
def coordinate_pair_exists : KDerivation (existsCode 11 (pairFormula 11 30 31).encode) :=
  pair_exists_with_names 30 31 11 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- The second witness is the ordered pair of the first witness and value. -/
def nested_pair_exists : KDerivation (existsCode 12 (pairFormula 12 11 32).encode) :=
  pair_exists_with_names 11 32 12 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- K can adjoin the nested edge object at 12 to the old graph at 6. -/
def extension_exists : KDerivation (existsCode 9 (adjoinCode 6 12 9 16)) := by
  have hlarge := (predicate_names_lt 6 12 17).2.2
  exact adjoin_graph_exists_fresh 6 12 17 16 9
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by omega)

private def adjoined_point : KDerivation (imp (adjoinCode 6 12 9 16) (member 9 12)) := by
  let f := namedBoth (.imp (.member 9 16) (namedEither (.equal 16 12) (.member 6 16)))
    (.imp (namedEither (.equal 16 12) (.member 6 16)) (.member 9 16))
  have hi := universalInstance 16 12 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (adjoinCode 6 12 9 16)
      (both (imp (member 9 12) (either (equal 12 12) (member 6 12)))
        (imp (either (equal 12 12) (member 6 12)) (member 9 12)))) := by
    simpa [f,namedBoth,namedEither,adjoinCode,Formula.encode,replace,rename,both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [adjoinCode 6 12 9 16] (adjoinCode 6 12 9 16) := .head [] _
  have hor : Context [adjoinCode 6 12 9 16] (either (equal 12 12) (member 6 12)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 12))
  exact .mp hor (Context.conjunctionRight (.mp ha (.closed hi')))

private def nested_edge : KDerivation
    (imp (both (member 9 12) (pairFormula 12 11 32).encode) (graphFormula 9 11 32).encode) := by
  let f : Formula := namedBoth (.member 9 19) (pairFormula 19 11 32)
  have hi := exists_variable_intro 19 12 f (by decide) (by decide) (by decide)
  have hr : replace 19 12 f = namedBoth (.member 9 12) (pairFormula 12 11 32) := by decide
  rw [hr] at hi
  change KDerivation (imp (both (member 9 12) (pairFormula 12 11 32).encode)
    (graphFormula 9 11 32).encode) at hi
  exact hi

/-- Supplied pair and adjunction witnesses give the actual new product triple. -/
def triple_from_witnesses : KDerivation (imp (pairFormula 11 30 31).encode
    (imp (pairFormula 12 11 32).encode
      (imp (adjoinCode 6 12 9 16) (tripleAt 9 30 31 32).encode))) := by
  let f : Formula := namedBoth (pairFormula 18 30 31) (graphFormula 9 18 32)
  have hi := exists_variable_intro 18 11 f (by decide) (by decide) (by decide)
  have hr : replace 18 11 f = namedBoth (pairFormula 11 30 31) (graphFormula 9 11 32) := by decide
  rw [hr] at hi
  have hi' : KDerivation (imp (both (pairFormula 11 30 31).encode (graphFormula 9 11 32).encode)
      (tripleAt 9 30 31 32).encode) := by
    simpa [f,tripleAt,namedBoth,Formula.encode,both,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 6 12 9 16,(pairFormula 12 11 32).encode,(pairFormula 11 30 31).encode]
  have ha : Context Γ (adjoinCode 6 12 9 16) := .head _ _
  have hp : Context Γ (pairFormula 12 11 32).encode := .hypothesis (by simp [Γ])
  have hq : Context Γ (pairFormula 11 30 31).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 12) := .mp ha (.closed adjoined_point)
  have he : Context Γ (graphFormula 9 11 32).encode :=
    .mp (Context.conjunctionIntro hm hp) (.closed nested_edge)
  exact .mp (Context.conjunctionIntro hq he) (.closed hi')


/-- K constructs both nested pair witnesses and a graph obtained by adjoining
that exact edge; the constructed graph contains the new product triple. The
old graph and values are arbitrary free inputs. -/
def single_triple_extension_exists : KDerivation (existsCode 11
    (both (pairFormula 11 30 31).encode (existsCode 12
      (both (pairFormula 12 11 32).encode (existsCode 9
        (both (adjoinCode 6 12 9 16) (tripleAt 9 30 31 32).encode)))))) := by
  let P : Formula := pairFormula 11 30 31
  let Q : Formula := pairFormula 12 11 32
  let A : Formula := namedAdjoin 6 12 9 16
  let T : Formula := tripleAt 9 30 31 32
  let R : Formula := namedBoth P Q
  let B : Formula := namedBoth A T
  have hAB : KDerivation (imp R.encode (imp A.encode B.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A.encode,R.encode]
    have ha : Context Γ A.encode := .head _ _
    have hr : Context Γ R.encode := .hypothesis (by simp [Γ])
    have hp : Context Γ P.encode := Context.conjunctionLeft hr
    have hq : Context Γ Q.encode := Context.conjunctionRight hr
    have ht : Context Γ T.encode := by
      simpa [P,Q,A,T,tripleAt,namedAdjoin,namedBoth,namedEither,Formula.encode,
        adjoinCode,both,neg,either] using
        (Context.mp ha (Context.mp hq (Context.mp hp (.closed triple_from_witnesses))))
    exact Context.conjunctionIntro ha ht
  have hA : KDerivation (existsCode 9 A.encode) := by
    simpa [A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either]
      using extension_exists
  have hP_Q_B : KDerivation (imp P.encode (imp Q.encode (existsCode 9 B.encode))) := by
    have hcong := conditionalExistsCongr 9 (R.vacuity 9 (by decide)) hAB
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Q.encode,P.encode]
    have hq : Context Γ Q.encode := .head _ _
    have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
    have hr : Context Γ R.encode := Context.conjunctionIntro hp hq
    exact .mp (.closed hA) (.mp hr (.closed hcong))
  let C : Formula := namedBoth Q (.ex 9 B)
  have hP_Q_C : KDerivation (imp P.encode (imp Q.encode C.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Q.encode,P.encode]
    have hq : Context Γ Q.encode := .head _ _
    have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
    have hex : Context Γ (existsCode 9 B.encode) := .mp hq (.mp hp (.closed hP_Q_B))
    exact Context.conjunctionIntro hq hex
  have hQ : KDerivation (existsCode 12 Q.encode) := nested_pair_exists
  have hP_C : KDerivation (imp P.encode (existsCode 12 C.encode)) := by
    have hcong := conditionalExistsCongr 12 (P.vacuity 12 (by decide)) hP_Q_C
    exact Context.closeEmpty (Context.deduction
      (.mp (.closed hQ) (.mp (Context.head [] _) (.closed hcong))))
  let D : Formula := namedBoth P (.ex 12 C)
  have hP_D : KDerivation (imp P.encode D.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hp : Context [P.encode] P.encode := .head [] _
    exact Context.conjunctionIntro hp (.mp hp (.closed hP_C))
  have hresult : KDerivation (existsCode 11 D.encode) :=
    .mp coordinate_pair_exists (existsCongr 11 hP_D)
  simpa [P,Q,A,T,B,C,D,R,namedAdjoin,namedBoth,namedEither,
    Formula.encode,adjoinCode,both,neg,either] using hresult

theorem single_triple_extension_exists_certificate :
    theoremCode (certificate single_triple_extension_exists) = existsCode 11
      (both (pairFormula 11 30 31).encode (existsCode 12
        (both (pairFormula 12 11 32).encode (existsCode 9
          (both (adjoinCode 6 12 9 16) (tripleAt 9 30 31 32).encode))))) :=
  certificate_correct single_triple_extension_exists

end PASoundness.PAtoCompactMultiplicationSingleTripleExtension
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.coordinate_pair_exists
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.nested_pair_exists
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.extension_exists
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.triple_from_witnesses

#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.single_triple_extension_exists
#print axioms PASoundness.PAtoCompactMultiplicationSingleTripleExtension.single_triple_extension_exists_certificate

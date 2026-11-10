import PASoundness.PAtoCompactKuratowskiTemporary
import PASoundness.PAtoCompactKuratowskiFresh
import PASoundness.PAtoCompactPairSpecified
import PASoundness.PAtoCompactTransitiveWitness

/-! K construction of a single represented Kuratowski pair with free endpoint
names 2 and 3. This does not construct a collection of pairs, an isomorphism
graph, quotient equality, or an interpretation of arithmetic. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiExists
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactSingletonSelector
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactPairSpecified
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiFresh
open PASoundness.PAtoCompactKuratowskiTemporary
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Assemble explicit singleton and pair witnesses into the displayed pair
formula, retaining the assembly implication as a proof premise. -/
def pair_exists_of_assembly
    (hpack : KDerivation (imp (singletonCode 2 23 22)
      (imp (pairCode 2 3 24 22) (imp (pairCode 23 24 19 22)
        (pairFormula 19 2 3).encode)))) :
    KDerivation (existsCode 19 (pairFormula 19 2 3).encode) := by
  let S := singletonCode 2 23 22
  let P := pairCode 2 3 24 22
  let O := pairCode 23 24 19 22
  let F := (pairFormula 19 2 3).encode
  let T := existsCode 19 F
  have hsV : KDerivation (imp S (allCode 19 S)) := by
    have h := (namedSingleton 2 23 22).vacuity 19 (by decide)
    simpa [S,namedSingleton,namedBoth,CompactNamed.Formula.encode,
      singletonCode,CompactProof.both,CompactProof.neg] using h
  have hpV : KDerivation (imp P (allCode 19 P)) := by
    have h := (namedPair 2 3 24 22).vacuity 19 (by decide)
    simpa [P,namedPair,namedBoth,namedEither,CompactNamed.Formula.encode,
      pairCode,CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hlocal : KDerivation (imp S (imp P T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,S]
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have himp : Context Γ (imp O F) := .mp hp (.mp hs (.closed hpack))
    have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
      intro h hh
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
      by_cases he : h = P
      · subst h; exact hpV
      · have he' : h = S := hh.resolve_left he
        subst h; exact hsV
    have hall : Context Γ (allCode 19 (imp O F)) := Context.generalize 19 hv himp
    have hex : Context Γ (existsCode 19 O) :=
      .closed (pair_exists_with_names 23 24 19 22 (by decide) (by decide)
        (by decide) (by decide) (by decide))
    exact exists_map_context hall hex
  let fST : CompactNamed.Formula := .imp (namedSingleton 2 23 22)
    (.ex 19 (pairFormula 19 2 3))
  have hv24 : KDerivation (imp (imp S T) (allCode 24 (imp S T))) := by
    have h := fST.vacuity 24 (by decide)
    simpa [fST,S,T,F,namedSingleton,namedBoth,CompactNamed.Formula.encode,
      singletonCode,CompactProof.both,CompactProof.neg] using h
  have hlocal' : KDerivation (imp P (imp S T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have hs : Context [S,P] S := Context.head _ _
    have hp : Context [S,P] P := .hypothesis (by simp)
    exact .mp hp (.mp hs (.closed hlocal))
  have hfromS : KDerivation (imp S T) := by
    apply Context.closeEmpty
    apply Context.existsElim hv24
    · exact .closed (.generalize 24 hlocal')
    · exact .closed (pair_exists_with_names 2 3 24 22 (by decide) (by decide)
        (by decide) (by decide) (by decide))
  have hs : KDerivation (existsCode 23 S) :=
    singleton_graph_exists_fresh 2 4 22 23 (by decide) (by decide) (by decide)
      (by unfold singletonPredicate CompactProof.equal Cantor.pair Cantor.triangle; decide)
      (by decide) (by decide) (by decide)
      (by unfold singletonPredicate CompactProof.equal Cantor.pair Cantor.triangle; decide)
  apply Context.closeEmpty
  exact Context.existsElim (pair_exists_helper_vacuity 23 (by simp))
    (.closed (.generalize 23 hfromS)) (.closed hs)

/-- K constructs the literal quotient proposal's relational pair for the
free endpoint names 2 and 3. -/
def pair_exists : KDerivation (existsCode 19 (pairFormula 19 2 3).encode) := by
  have h := assemble_temporary 19 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  apply pair_exists_of_assembly
  simpa [singletonAt,pairAt,namedSingleton,namedPair,namedBoth,namedEither,
    singletonCode,pairCode,CompactNamed.Formula.encode,CompactProof.both,
    CompactProof.neg,CompactDerivations.either] using h

theorem pair_exists_certificate : theoremCode (certificate pair_exists) =
    existsCode 19 (pairFormula 19 2 3).encode := certificate_correct pair_exists

end PASoundness.PAtoCompactKuratowskiExists

#print axioms PASoundness.PAtoCompactKuratowskiExists.pair_exists_of_assembly
#print axioms PASoundness.PAtoCompactKuratowskiExists.pair_exists
#print axioms PASoundness.PAtoCompactKuratowskiExists.pair_exists_certificate

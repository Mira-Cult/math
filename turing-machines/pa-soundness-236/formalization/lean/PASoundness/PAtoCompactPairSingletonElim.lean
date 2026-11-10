import PASoundness.PAtoCompactSingleton
import PASoundness.PAtoCompactUnorderedPair

/-! Eliminate an explicit K singleton witness from a supplied local proof of
an existential pair graph. Existence and correctness of the local pair
construction are not asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairSingletonElim
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSingletonSelector PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A local K proof from a singleton graph to an existential pair graph can
eliminate that singleton witness. All selector and conclusion freshness
conditions are explicit; the conclusion need not use distinct element names. -/
def eliminate_singleton_for_pair (a b s d q r t : Nat)
    (hta : t ≠ a) (hqt : q ≠ t) (hqa : q ≠ a)
    (hqc : q ≠ singletonPredicate a t)
    (hsa : s ≠ a) (hst : s ≠ t) (hsq : s ≠ q)
    (hsc : s ≠ singletonPredicate a t)
    (hsb : s ≠ b) (hsd : s ≠ d) (hsr : s ≠ r)
    (hlocal : KDerivation (imp (singletonCode a s q)
      (existsCode d (pairCode a b d r)))) :
    KDerivation (existsCode d (pairCode a b d r)) := by
  let E := existsCode d (pairCode a b d r)
  let f : CompactNamed.Formula := .ex d (namedPair a b d r)
  have hn : s ∉ f.names := by
    simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.names,
      hsa, hsb, hsd, hsr]
  have hv : KDerivation (imp E (allCode s E)) := by
    have h := f.vacuity s hn
    simpa [f, E, namedPair, namedBoth, namedEither, pairCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  have hsing : KDerivation (existsCode s (singletonCode a s q)) :=
    singleton_graph_exists_fresh a t q s hta hqt hqa hqc hsa hst hsq hsc
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize s hlocal)) (.closed hsing)

theorem eliminate_singleton_for_pair_certificate (a b s d q r t : Nat)
    (hta : t ≠ a) (hqt : q ≠ t) (hqa : q ≠ a)
    (hqc : q ≠ singletonPredicate a t)
    (hsa : s ≠ a) (hst : s ≠ t) (hsq : s ≠ q)
    (hsc : s ≠ singletonPredicate a t)
    (hsb : s ≠ b) (hsd : s ≠ d) (hsr : s ≠ r)
    (hlocal : KDerivation (imp (singletonCode a s q)
      (existsCode d (pairCode a b d r)))) :
    theoremCode (certificate (eliminate_singleton_for_pair a b s d q r t
      hta hqt hqa hqc hsa hst hsq hsc hsb hsd hsr hlocal)) =
      existsCode d (pairCode a b d r) :=
  certificate_correct (eliminate_singleton_for_pair a b s d q r t
    hta hqt hqa hqc hsa hst hsq hsc hsb hsd hsr hlocal)

end PASoundness.PAtoCompactPairSingletonElim

#print axioms PASoundness.PAtoCompactPairSingletonElim.eliminate_singleton_for_pair
#print axioms PASoundness.PAtoCompactPairSingletonElim.eliminate_singleton_for_pair_certificate

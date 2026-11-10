import PASoundness.PAtoCompactRestrictionEndpointPair
import PASoundness.PAtoCompactGraphRestriction

/-! Eliminate both endpoint witnesses of the literal restriction predicate.
All quantifier-vacuity data is supplied as explicit finite K proofs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEndpointElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictionEndpointPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From the literal pair and endpoint predicate, K derives endpoint
membership, provided explicit vacuity proofs permit eliminating both
endpoint names. The proof retains the same pair witness 19 throughout. -/
def endpoints_from_predicate (x y u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup)
    (vA25 : KDerivation (imp (pairFormula 19 u v).encode
      (allCode 25 (pairFormula 19 u v).encode)))
    (vA26 : KDerivation (imp (pairFormula 19 u v).encode
      (allCode 26 (pairFormula 19 u v).encode)))
    (vX26 : KDerivation (imp (member x 25) (allCode 26 (member x 25))))
    (vT25 : KDerivation (imp (both (member x u) (member y v))
      (allCode 25 (both (member x u) (member y v)))))
    (vT26 : KDerivation (imp (both (member x u) (member y v))
      (allCode 26 (both (member x u) (member y v))))) :
    KDerivation (imp (pairFormula 19 u v).encode
      (imp (edgePredicate 19 x y).encode (both (member x u) (member y v)))) := by
  let A := (pairFormula 19 u v).encode
  let X := member x 25
  let Y := member y 26
  let C := (pairFormula 19 25 26).encode
  let T := both (member x u) (member y v)
  let B := both Y C
  let E := existsCode 26 B
  let D := both X E
  have hinner : Context [X,A] (imp B T) := by
    apply Context.deduction
    have hb : Context [B,X,A] B := Context.head _ _
    have hx : Context [B,X,A] X := .hypothesis (by simp)
    have ha : Context [B,X,A] A := .hypothesis (by simp)
    have hy : Context [B,X,A] Y := Context.conjunctionLeft hb
    have hc : Context [B,X,A] C := Context.conjunctionRight hb
    exact .mp ha (.mp hc (.mp hy (.mp hx (.closed (endpoints_of_shared_pair x y u v pairFresh)))))
  have hctx26 : ∀ q, q ∈ [X,A] → KDerivation (imp q (allCode 26 q)) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = X
    · subst q
      exact vX26
    · have he' : q = A := hq.resolve_left he
      subst q
      exact vA26
  have hall26 : Context [X,A] (allCode 26 (imp B T)) :=
    Context.generalize 26 hctx26 hinner
  have hstep26 : Context [A] (imp X (imp E T)) := by
    apply Context.deduction
    apply Context.deduction
    have he : Context [E,X,A] E := Context.head _ _
    exact Context.existsElim vT26 (Context.under hall26 E) he
  have hstep25 : Context [A] (imp D T) := by
    apply Context.deduction
    have hd : Context [D,A] D := Context.head _ _
    have hx : Context [D,A] X := Context.conjunctionLeft hd
    have he : Context [D,A] E := Context.conjunctionRight hd
    exact .mp he (.mp hx (Context.under hstep26 D))
  have hctx25 : ∀ q, q ∈ [A] → KDerivation (imp q (allCode 25 q)) := by
    intro q hq
    have hq' : q = A := by simpa using hq
    subst q
    exact vA25
  have hall25 : Context [A] (allCode 25 (imp D T)) :=
    Context.generalize 25 hctx25 hstep25
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have he : Context [(edgePredicate 19 x y).encode,A] (existsCode 25 D) := by
    change Context [(edgePredicate 19 x y).encode,A] (edgePredicate 19 x y).encode
    exact Context.head _ _
  exact Context.existsElim vT25 (Context.under hall25 (edgePredicate 19 x y).encode) he

end PASoundness.PAtoCompactRestrictionEndpointElim

#print axioms PASoundness.PAtoCompactRestrictionEndpointElim.endpoints_from_predicate

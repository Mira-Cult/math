import PASoundness.PAtoCompactGraphRestriction
import PASoundness.PAtoCompactKuratowskiFresh
import PASoundness.PAtoCompactAdjunction

/-! Capture-safe introduction of arbitrary endpoint names into the literal
restriction predicate. No graph existence or isomorphism is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEndpointIntro
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactKuratowskiFresh PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Explicit endpoint witnesses imply the literal existential restriction
predicate. Each of q,x,y,u,v must avoid the internal labels 20,21,22,25,26;
the five displayed names may otherwise coincide. -/
def endpoint_intro (q x y u v : Nat)
    (fresh : ∀ z ∈ [q,x,y,u,v], z ∉ ({20,21,22,25,26} : Finset Nat)) :
    KDerivation (imp (member x u) (imp (member y v)
      (imp (pairFormula q u v).encode (edgePredicate q x y).encode))) := by
  have avoid (z : Nat) (hz : z ∈ [q,x,y,u,v]) (i : Nat)
      (hi : i ∈ ({20,21,22,25,26} : Finset Nat)) : z ≠ i := by
    intro he; subst z; exact fresh i hz hi
  have q25 : q ≠ 25 := avoid q (by simp) 25 (by simp)
  have q26 : q ≠ 26 := avoid q (by simp) 26 (by simp)
  have x25 : x ≠ 25 := avoid x (by simp) 25 (by simp)
  have y25 : y ≠ 25 := avoid y (by simp) 25 (by simp)
  have y26 : y ≠ 26 := avoid y (by simp) 26 (by simp)
  have u20 : u ≠ 20 := avoid u (by simp) 20 (by simp)
  have u21 : u ≠ 21 := avoid u (by simp) 21 (by simp)
  have u22 : u ≠ 22 := avoid u (by simp) 22 (by simp)
  have u25 : u ≠ 25 := avoid u (by simp) 25 (by simp)
  have u26 : u ≠ 26 := avoid u (by simp) 26 (by simp)
  have v20 : v ≠ 20 := avoid v (by simp) 20 (by simp)
  have v21 : v ≠ 21 := avoid v (by simp) 21 (by simp)
  have v22 : v ≠ 22 := avoid v (by simp) 22 (by simp)
  have v26 : v ≠ 26 := avoid v (by simp) 26 (by simp)
  let R := namedBoth (.member y 26) (pairFormula q u 26)
  let S := namedBoth (.member x 25) (.ex 26 (namedBoth (.member y 26) (pairFormula q 25 26)))
  have hi26 := exists_variable_intro 26 v R (Ne.symm v26)
    (by simp [R, namedBoth, Formula.binders, pair_binders])
    (by simp [R, namedBoth, Formula.binders, pair_binders, v20, v21, v22])
  have hR : (CompactNamed.replace 26 v R).encode =
      (namedBoth (.member y v) (pairFormula q u v)).encode := by
    simp [R, pair_formula_named, PAtoCompactSingleton.namedSingleton,
      PAtoCompactUnorderedPair.namedPair, namedBoth, namedEither, CompactNamed.replace,
      CompactNamed.rename, Formula.encode, q26, y26, u26]
  rw [hR] at hi26
  have hi25 := exists_variable_intro 25 u S (Ne.symm u25)
    (by simp [S, namedBoth, Formula.binders, pair_binders])
    (by simp [S, namedBoth, Formula.binders, pair_binders, u20, u21, u22, u26])
  have hS : (CompactNamed.replace 25 u S).encode =
      (namedBoth (.member x u) (.ex 26 R)).encode := by
    simp [S, R, pair_formula_named, PAtoCompactSingleton.namedSingleton,
      PAtoCompactUnorderedPair.namedPair, namedBoth, namedEither, CompactNamed.replace,
      CompactNamed.rename, Formula.encode, q25, x25, y25]
  rw [hS] at hi25
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula q u v).encode, member y v, member x u]
  have hp : Context Γ (pairFormula q u v).encode := .head _ _
  have hy : Context Γ (member y v) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member x u) := .hypothesis (by simp [Γ])
  have hrv : Context Γ (namedBoth (.member y v) (pairFormula q u v)).encode := by
    simpa [namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using Context.conjunctionIntro hy hp
  have hr : Context Γ (Formula.ex 26 R).encode := .mp hrv (.closed hi26)
  have hsv : Context Γ (namedBoth (.member x u) (.ex 26 R)).encode := by
    simpa [namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using Context.conjunctionIntro hx hr
  have hs : Context Γ (Formula.ex 25 S).encode := .mp hsv (.closed hi25)
  simpa only [edgePredicate, S] using hs

theorem endpoint_intro_certificate (q x y u v : Nat)
    (fresh : ∀ z ∈ [q,x,y,u,v], z ∉ ({20,21,22,25,26} : Finset Nat)) :
    theoremCode (certificate (endpoint_intro q x y u v fresh)) =
      imp (member x u) (imp (member y v)
        (imp (pairFormula q u v).encode (edgePredicate q x y).encode)) :=
  certificate_correct (endpoint_intro q x y u v fresh)

end PASoundness.PAtoCompactRestrictionEndpointIntro

#print axioms PASoundness.PAtoCompactRestrictionEndpointIntro.endpoint_intro
#print axioms PASoundness.PAtoCompactRestrictionEndpointIntro.endpoint_intro_certificate

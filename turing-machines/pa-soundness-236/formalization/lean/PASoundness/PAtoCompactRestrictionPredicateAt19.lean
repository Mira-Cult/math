import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactGraphRestriction
import PASoundness.PAtoCompactKuratowskiSyntax

/-! K filter instantiation at the graph's pair-witness label 19. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionPredicateAt19
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Replacing the filter's test label by 19 yields the exact endpoint
predicate at 19. The pair and endpoint binders are explicitly kept distinct
from both labels; the set-name labels are not rewritten. -/
theorem edge_predicate_replace (t x y : Nat)
    (fresh : [t,x,y,19,20,21,22,25,26].Nodup) :
    replace t 19 (edgePredicate t x y) = edgePredicate 19 x y := by
  have htx : t ≠ x := by intro he; subst t; simp at fresh
  have hty : t ≠ y := by intro he; subst t; simp at fresh
  have ht20 : t ≠ 20 := by intro he; subst t; simp at fresh
  have ht21 : t ≠ 21 := by intro he; subst t; simp at fresh
  have ht22 : t ≠ 22 := by intro he; subst t; simp at fresh
  have ht25 : t ≠ 25 := by intro he; subst t; simp at fresh
  have ht26 : t ≠ 26 := by intro he; subst t; simp at fresh
  simp [edgePredicate, namedBoth, pair_formula_named, namedSingleton, namedPair, namedEither,
    replace, rename, Ne.symm htx, Ne.symm hty, Ne.symm ht20, Ne.symm ht21,
    Ne.symm ht22, Ne.symm ht25, Ne.symm ht26]

/-- Given the displayed endpoint filter and an actual filtered member at
the pair-witness name 19, K derives its exact endpoint predicate. This is a
finite proof object; it does not eliminate the endpoint existentials or
establish endpoint membership of a differently named pair. -/
def filter_member_predicate (g h t x y : Nat)
    (fresh : [g,h,t,x,y,19,20,21,22,25,26].Nodup) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (member h 19) (edgePredicate 19 x y).encode)) := by
  have htg : t ≠ g := by intro he; subst t; simp at fresh
  have hth : t ≠ h := by intro he; subst t; simp at fresh
  have ht19 : t ≠ 19 := by intro he; subst t; simp at fresh
  have ht20 : t ≠ 20 := by intro he; subst t; simp at fresh
  have ht21 : t ≠ 21 := by intro he; subst t; simp at fresh
  have ht22 : t ≠ 22 := by intro he; subst t; simp at fresh
  have ht25 : t ≠ 25 := by intro he; subst t; simp at fresh
  have ht26 : t ≠ 26 := by intro he; subst t; simp at fresh
  have hbind : t ∉ (edgePredicate t x y).binders := by
    simp [edgePredicate, namedBoth, pair_formula_named, namedSingleton, namedPair, namedEither,
      Formula.binders, ht20, ht21, ht22, ht25, ht26]
  have h19bind : 19 ∉ (edgePredicate t x y).binders := by
    simp [edgePredicate, namedBoth, pair_formula_named, namedSingleton, namedPair, namedEither,
      Formula.binders]
  have hsub : [t,x,y,19,20,21,22,25,26].Nodup := fresh.tail.tail
  have hi := filter_at g h t 19 (edgePredicate t x y) htg hth ht19 hbind h19bind
  rw [edge_predicate_replace t x y hsub] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let F := filterGraph g h t (edgePredicate t x y).encode
  let M := member h 19
  have hf : Context [M,F] F := .hypothesis (by simp)
  have hm : Context [M,F] M := .head _ _
  have hc : Context [M,F] (both (member g 19) (edgePredicate 19 x y).encode) :=
    .mp hm (Context.conjunctionLeft (.mp hf (.closed hi)))
  exact Context.conjunctionRight hc

theorem filter_member_predicate_certificate (g h t x y : Nat)
    (fresh : [g,h,t,x,y,19,20,21,22,25,26].Nodup) :
    theoremCode (certificate (filter_member_predicate g h t x y fresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (member h 19) (edgePredicate 19 x y).encode) :=
  certificate_correct (filter_member_predicate g h t x y fresh)

end PASoundness.PAtoCompactRestrictionPredicateAt19

#print axioms PASoundness.PAtoCompactRestrictionPredicateAt19.filter_member_predicate

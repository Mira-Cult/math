import PASoundness.PAtoCompactKuratowskiInjectivity

/-! Equality transport for the designated new pair object in the conditional
successor-congruence construction. This is a finite K derivation, not graph
existence, collection, or a quotient law. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruencePairAlias
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiInjectivity

/-- If the selected pair object 19 equals the supplied new object 11, its
coordinates 2,3 agree with the new pair's 0,1. Pair witnesses bind only
20,21,22, so replacing 19 by 11 is capture-safe. The stated equality is an
object-level premise; the variable labels 0,1,2,3 remain distinct syntactically
but their interpreted values may coincide. -/
def new_pair_alias : KDerivation (imp (equal 19 11)
    (imp (pairFormula 19 2 3).encode (imp (pairFormula 11 0 1).encode
      (both (equal 2 0) (equal 3 1))))) := by
  have hrepl : CompactNamed.replace 19 11 (pairFormula 19 2 3) = pairFormula 11 2 3 := by decide
  have ht := (CompactNamed.equalityReplace 19 11 (pairFormula 19 2 3)
    (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 11 0 1).encode,(pairFormula 19 2 3).encode,equal 19 11]
  have he : Context Γ (equal 19 11) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 2 3).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (pairFormula 11 0 1).encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (pairFormula 11 2 3).encode := .mp ha (.mp he (.closed ht))
  exact .mp hb (.mp ha' (.closed (pair_coordinates 11 2 3 0 1 (by decide))))

theorem new_pair_alias_certificate : theoremCode (certificate new_pair_alias) =
    imp (equal 19 11) (imp (pairFormula 19 2 3).encode (imp (pairFormula 11 0 1).encode
      (both (equal 2 0) (equal 3 1)))) := certificate_correct new_pair_alias

end PASoundness.PAtoCompactSuccCongruencePairAlias

#print axioms PASoundness.PAtoCompactSuccCongruencePairAlias.new_pair_alias
#print axioms PASoundness.PAtoCompactSuccCongruencePairAlias.new_pair_alias_certificate
